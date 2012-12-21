{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}

-- | A pass to get us down to an executable GPU program.

module Data.Array.Accelerate.BackendKit.Phase3.LowerGPUIR (lowerGPUIR) where

import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                  (Const(..), Type(..), Prim(..), NumPrim(..), ScalarPrim(..), IntPrim(..),Var)
-- import qualified Data.Array.Accelerate.SimpleAST as S
import qualified Data.Set                        as S
import           Data.Array.Accelerate.BackendKit.IRs.GPUIR         as G
import           Data.Array.Accelerate.BackendKit.IRs.Metadata  (ArraySizeEstimate(..), FreeVars(..))
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName, fragileZip, quotI)
import           Control.Monad.State.Strict (runState)
import           Debug.Trace

--------------------- CONSTANTS : Configuration Parameters ---------------------

-- | How big should a work-group for folding purposes?  It must be big
-- enough to fill all SIMD lanes of all streaming multiprocessors on
-- the GPU.
workGroupSize :: Int
workGroupSize = 1024


--------------------------------------------------------------------------------

-- | Desugar Generate and Fold into explicit Kernels and NewArrays.
lowerGPUIR :: GPUProg (ArraySizeEstimate,FreeVars) -> GPUProg ()
lowerGPUIR prog@GPUProg{progBinds, uniqueCounter} =
  prog {
    progBinds    = binds, 
    uniqueCounter= newCounter
  }
  where
    (binds,newCounter) = runState (doBinds prog progBinds) uniqueCounter


-- This procedure keeps around a "size map" from array values names to
-- their number of elements.
doBinds :: GPUProg (ArraySizeEstimate,FreeVars) ->
           [GPUProgBind (ArraySizeEstimate,FreeVars)] -> GensymM [GPUProgBind ()]
doBinds prog [] = return []
doBinds prog (pb@GPUProgBind { outarrs, evtid, evtdeps,
                               decor=(sz,FreeVars arrayOpFvs), op } : rest) = do  
  let deflt = do rst <- doBinds prog rest
                 return $ pb{decor=()} : rst
  case op of
     Use  _       -> deflt
     Cond _ _ _   -> deflt
     ScalarCode _ -> deflt

     -- A Generate breaks down into a separate NewArray and Kernel:      
     -- Assumes trivial (duplicatable) els:
     Generate els (Lam iterargs bod) -> do
       -- Here is where we establish the protocol on additional kernel arguments.
       -- Kernels take their index argument(s) PLUS free vars:
       let iterVs = map (\ (v, _, TInt) -> v) iterargs
           iters  = fragileZip iterVs els

           -- After this transformation in this pass, the output variable itself becomes a "free var":
           freebinds' = outarr1 : corefreebinds
           
       newevt <- genUniqueWith "evtNew"
       rst <- doBinds prog rest
       return $
         GPUProgBind newevt [] outarrs () (NewArray (foldl mulI one els)) :
         GPUProgBind evtid (newevt:evtdeps) [] ()
                     (Kernel iters (Lam freebinds' (doBod iterVs bod))
                                   (map (EVr . fst3) freebinds')) :
         rst 

     --------------------------------------------------------------------------------
     -- Here is a serial fold as an example:
     -- TODO FINISHME -- make this into the three-phase parallel fold!
     Fold (Lam [(v,_,ty1),(w,_,ty2)] bod) [initE] inV (ConstantStride _) -> do
#if 1
       -- Not supporting tuple (multiple) accumulators:
       let (ScalarBlock locals [res] stmts) = bod
           Just upstream = lookupProgBind inV (progBinds prog)
           inSz = getSizeOfPB upstream
       -- We need a bunch of temporaries!
       ix     <- genUnique
       ix2    <- genUnique
       newevt <- genUniqueWith "evtFldArr"
       sharedAccums   <- genUniqueWith "sharedAccums"
       -- The old arrayOpFvs are only for the kernel (the Lam) not for the extra bits that are
       -- parameters to the fold or are implicit.
       let localmembind = (sharedAccums, Local, TArray 1 ty2)

           newfvs = S.toList $ S.insert inV $
                    S.union (expFreeVars inSz) (expFreeVars initE)
           -- The new free variables are all top-level, so we use that fact to recover their types:
           newbinds = map (retrieveTopLvlBind prog) newfvs
           almostAllBinds = outarr1 : newbinds ++ corefreebinds
           allfreebinds = localmembind : almostAllBinds
           -- The sharedAccums variable becomes a kernel argument and contains workGroupSize elements:
           kernargs     = EUnInitArray ty1 workGroupSize : 
                          map (EVr . fst3) almostAllBinds

           newop = Kernel [(ix2, inSz)] kernbod kernargs
           workGroupSizeE = EConst (I workGroupSize)
           kernbod = Lam allfreebinds $
              ScalarBlock ((v,Default,ty1) : (w,Default,ty2) : locals) [] $ 
              -------------------------Begin Kernel----------------------------
              [
               SComment "This function implements a Fold.  First we init our accumulator with the seed value:",
               SSet w initE,
               SComment "Next, each thread serially folds a chunk of the inputs:", 
               SCond (EPrimApp TBool (SP Eq) [EGetGlobalID 0, zero])
                 [forUpTo ix (EPrimApp TInt (IP IDiv) [inSz,workGroupSizeE]) $
                    SSet v (EIndexScalar inV (EVr ix)) :
                    stmts ++ -- This will consume v & w and write res.
                    [SSet w (EVr res),
                     SArrSet sharedAccums (remI (EVr ix) workGroupSizeE) (EVr res),
                     SArrSet sharedAccums zero (EVr res)]]
                 [SNoOp],
               SSynchronizeThreads,
               SComment "Finally, we (temporarily) have a single thread sum over shared memory:",              
               (forUpTo ix workGroupSizeE $
                    SComment ("We continue using "++show w++" as an accumulator:") :
                    SSet v (EIndexScalar sharedAccums (EVr ix)) :
                    stmts ++ -- This will consume v & w and write res.
                    [SSet w (EVr res)]
                    ),
               SArrSet arrnm zero (EIndexScalar sharedAccums zero)
              ]
              --------------------------End Kernel-----------------------------

       rst <- doBinds prog rest
       return $ 
         GPUProgBind newevt [] outarrs () (NewArray one) :
         GPUProgBind evtid (newevt:evtdeps) [] () newop : rst
#else       
       -- Not supporting tuple (multiple) accumulators:
       let (ScalarBlock locals [res] stmts) = bod
           Just upstream = lookupProgBind inV (progBinds prog)
           inSz = getSizeOfPB upstream
       forloop <- forUpToM inSz $ \ ix ->
                    SSet v (EIndexScalar inV (EVr ix)) :
                    stmts ++ -- This will consume v & w and write res.
                    [SSet w (EVr res)]
       -- The old arrayOpFvs are only for the kernel (the Lam) not for the extra bits that are
       -- parameters to the fold or are implicit.
       let newfvs = S.insert inV $
                    S.union (expFreeVars inSz) $
                    S.union (expFreeVars init)
                            (S.fromList arrayOpFvs)
       ix2 <- genUnique
       let newop = Generate [one] $ Lam [(ix2,G.Default,TInt)] $
                   ScalarBlock ((v,G.Default,ty1) : (w,G.Default,ty2) : locals) [w] $
                     [SSet w init,
                      forloop]

       -- A little trick.  Here we put it back through the wash again
       -- to get rid of the Generate we just introduced:
       doBinds prog (pb{ decor=(sz,FreeVars$ S.toList newfvs), op = newop } : rest)
#endif

     _ -> error$"LowerGPUIR.hs/doBinds: not handled: "++show op
 where
   [outarr1@(arrnm,_spc,_ty)] = outarrs -- Touch this and you make the one-output-array assumption!

   -- All the free variables must be explicitly passed to the kernel:
   corefreebinds = map
               -- We do a bit of digging here to find the type of each freevar:
               (\fv -> case lookupProgBind fv (progBinds prog) of 
                        Nothing -> error$"variable not in progbinds: "++show fv
                        Just (GPUProgBind {outarrs=arrVs}) ->
                          let (Just tyy) = lookup fv (map (\(a,_,b) ->(a,b)) arrVs) in
                          (fv, typeToAddrSpc tyy, tyy)
               )
               arrayOpFvs
               
   -- Convert a Generate body into a Kernel body.  Rather than
   -- returning a value, this writes it to an output arr.
   doBod [ixV] (ScalarBlock bnds results stmts) =
     case results of
       [outv] -> ScalarBlock bnds []
                 (stmts ++ [SArrSet arrnm (EVr ixV) (EVr outv)])
       ls -> error$"LowerGPUIR.hs/doBod: not handling multi-result Generates presently: "++show ls

   doBod indexVs _ = error$"LowerGPUIR.hs/doBod: handling only 1D Generates, not dimension "++show (length indexVs)




--------------------------------------------------------------------------------


mulI :: Exp -> Exp -> Exp
mulI (EConst (I 0)) _ = EConst (I 0)
mulI _ (EConst (I 0)) = EConst (I 0)
mulI (EConst (I 1)) n = n
mulI n (EConst (I 1)) = n
mulI n m                = EPrimApp TInt (NP Mul) [n,m]


typeToAddrSpc :: Type -> MemLocation
typeToAddrSpc (TArray _ _) = Global
typeToAddrSpc _            = Default


-- | Build a simple for-loop from 0 up to limit-1:
forUpToM :: Exp -> (Var -> [Stmt]) -> GensymM Stmt
forUpToM limit bodfn = do ix <- genUnique
                          return $ forUpTo ix limit (bodfn ix)

forUpTo :: Var -> Exp -> [Stmt] -> Stmt
forUpTo ix limit bod = 
    SFor ix (zero)
            (EPrimApp TInt (SP Lt)   [EVr ix, limit])
            (EPrimApp TInt (NP Add)  [EVr ix, EConst (I 1)])
         bod



---------------------------------------------------------------------
-- HACK: This is incomplete!  We need a general-purpose way of getting
-- the size of arrays at this phase in the compiler.  To do this
-- properly OneDimensionalize will need to be modified.

 -- Get an expression representing the size of an output array:
getSizeE :: TopLvlForm -> Exp
getSizeE ae = 
  case ae of 
    Generate [ex] _ -> ex
    _ -> error$"LowerGPUIR.hs.hs/getSizeE: cannot handle this yet: "++show ae

getSizeOfPB :: GPUProgBind (ArraySizeEstimate,FreeVars) -> Exp
getSizeOfPB GPUProgBind{ decor=(sz,_), op } =
  case sz of
    KnownSize ls -> EConst (I (product ls))
    UnknownSize  -> getSizeE op

fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a

zero :: Exp
zero = EConst (I 0)

one :: Exp
one  = EConst (I 1)


-- topLevelExpType :: Show a => t -> a -> t1
-- topLevelExpType prog ex = error$"FINISHME: need to get the type of top level expr: "++show ex

-- (\vr -> (vr, Default, topLevelExpType prog (EVr vr)))


retrieveTopLvlBind :: GPUProg t -> Var -> (Var, MemLocation, Type)
retrieveTopLvlBind GPUProg{progBinds} vr = loop progBinds
 where
   loop [] = error$"Could not find top-level binding for variable: "++show vr
   loop (GPUProgBind{outarrs} : rest) = 
     case lookup3 vr outarrs of
       Nothing -> loop rest
       Just x  -> x

lookup3 :: Eq a => a -> [(a, t, t1)] -> Maybe (a, t, t1)
lookup3 a [] = Nothing
lookup3 a (hd@(b,_,_) : rst) | a == b    = Just hd
                             | otherwise = lookup3 a rst


modI :: Exp -> Exp -> Exp
modI n m = EPrimApp TInt (IP Mod) [n,m]


remI :: Exp -> Exp -> Exp
remI _ (EConst (I 1)) = EConst (I 0)
remI (EConst (I n)) (EConst (I m)) = EConst$ I$ rem n m
remI n m              = EPrimApp TInt (IP Rem) [n,m]
