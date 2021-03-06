{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A pass to remove the last two non-Kernel GPU forms and therefor
-- get down to an executable GPU program.

module Data.Array.Accelerate.BackendKit.Phase3.DesugarFoldScan (desugarFoldScan) where

import           Control.Monad.State.Strict (runState)
import qualified Data.Map as M
import qualified Data.Set as S

import           Data.Array.Accelerate.BackendKit.IRs.GPUIR         as G
import           Data.Array.Accelerate.BackendKit.IRs.Metadata  (FreeVars(..))
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName, fragileZip)
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                   (Const(..), Type(..), Prim(..), NumPrim(..), ScalarPrim(..), Var, TrivialExp(..))
                  
--------------------- CONSTANTS : Configuration Parameters ---------------------

-- | How big should a work-group for folding purposes?  It must be big
-- enough to fill all SIMD lanes of all streaming multiprocessors on
-- the GPU.
workGroupSize :: Int
workGroupSize = 1024

--------------------------------------------------------------------------------

-- | Desugar Generate and Fold into explicit Kernels and NewArrays.
desugarFoldScan :: GPUProg FreeVars -> GPUProg FreeVars
desugarFoldScan prog@GPUProg{progBinds, uniqueCounter, sizeEnv} =
  prog {
    progBinds    = binds, 
    uniqueCounter= newCounter
  }
  where
    (binds,newCounter) = runState (doBinds sizeEnv prog progBinds) uniqueCounter


-- This procedure keeps around a "size map" from array values names to
-- their number of elements.
doBinds ::          M.Map Var (Type,TrivialExp) ->
                    GPUProg     (FreeVars) -> 
                   [GPUProgBind (FreeVars)] ->
           GensymM [GPUProgBind (FreeVars)]
doBinds _ _ [] = return []
doBinds sizeEnv prog (pb@GPUProgBind { decor=(FreeVars arrayOpFvs), op } : rest) = do  
  let deflt = do rst <- doBinds sizeEnv prog rest
                 return $ pb : rst
  case op of
     Use  _        -> deflt
     Use' _ _ _    -> deflt
     Cond _ _ _    -> deflt
     ScalarCode _  -> deflt
     GenManifest _ -> deflt
     NewArray _    -> deflt
     Kernel {}     -> deflt
--     Scan _ _ _ _ -> error "DesugarFoldScan.hs/doBinds: FINISHME - need to handle "
     
     --------------------------------------------------------------------------------
--     Fold (Lam [(v,_,ty1),(w,_,ty2)] bod) [initE] inV (ConstantStride _) -> do
     GenReduce {} -> do
       error "DesugarFoldScan.hs : Rewrite for GenReduce"
#if 0
-- PARALLEL REDUCTION, UNFINISHED:    
       -- Not supporting tuple (multiple) accumulators:
       let (ScalarBlock locals [res] stmts) = bod
           inSz = getSizeE inV
       -- We need a bunch of temporaries!
       ix           <- genUniqueWith "ix"
       ix2          <- genUniqueWith "ix"
       offset       <- genUniqueWith "offset"
       newevt       <- genUniqueWith "evtFldArr"
       sharedAccums <- genUniqueWith "sharedAccums"
       numthreads   <- genUniqueWith "numThrds"

       -- The old arrayOpFvs are only for the kernel (the Lam) not for the extra bits that are
       -- parameters to the fold or are implicit.
       let localmembind = (sharedAccums, Local, TArray 1 ty2)

           newfvs = S.toList $ S.insert inV $
                    S.union (expFreeVars inSz) (expFreeVars initE)
           -- The new free variables are all top-level, so we use that fact to recover their types:
           newbinds = map (retrieveTopLvlBind prog) newfvs
           -- FIXME -- USE sizeEnv instead 


           almostAllBinds = outarr1 : newbinds ++ corefreebinds
           allfreebinds = localmembind : almostAllBinds
           -- The sharedAccums variable becomes a kernel argument and contains workGroupSize elements:
           kernargs     = EUnInitArray ty1 workGroupSize : 
                          map (EVr . fst3) almostAllBinds

           newop = Kernel [(ix2, EVr numthreads)] kernbod kernargs
           workGroupSizeE = EConst (I workGroupSize)
           kernbod = Lam allfreebinds $
              ScalarBlock ((v,Default,ty1) : (w,Default,ty2) : (offset,Default,TInt) : locals) [] $ 
              -------------------------Begin Kernel----------------------------
              [
               SComment "This function implements a Fold.  First we init our accumulator with the seed value:",
               SSet w initE,
               SSet offset (mulI (EGetGlobalID 0) workGroupSizeE), 
               
               SComment "Next, each thread serially folds a chunk of the inputs:", 
               forUpTo ix (EPrimApp TInt (IP Quot) [inSz,workGroupSizeE]) $
                    SSet v (EIndexScalar inV (addI (EVr offset) (EVr ix))) :
                    stmts ++ -- This will consume v & w and write res.
                    [SSet w (EVr res)],
               SArrSet sharedAccums (EGetGlobalID 0) (EVr w),
               SSynchronizeThreads,
               
               SComment "Finally, we (temporarily) have a single thread sum over shared memory:",
               SCond (EPrimApp TBool (SP Eq) [EGetGlobalID 0, zero])
                     [forUpTo ix workGroupSizeE $
                        SComment ("We continue using "++show w++" as an accumulator:") :
                        SSet v (EIndexScalar sharedAccums (EVr ix)) :
                        stmts ++ -- This will consume v & w and write res.
                        [SSet w (EVr res)]] [],
               SArrSet arrnm zero (EVr w)
              ]
              --------------------------End Kernel-----------------------------

       rst <- doBinds sizeEnv prog rest
       scalarBind <- mkScalarBind numthreads TInt (minI inSz workGroupSizeE)
       return $ 
         GPUProgBind newevt [] outarrs () (NewArray one) :
         scalarBind : 
         GPUProgBind evtid (newevt:evtdeps) [] () newop : rst
-- else       
       -- Here is a serial fold as an example:
       ------------------------------------------------------------
       -- Not supporting tuple (multiple) accumulators:
       let (ScalarBlock locals [res] stmts) = bod
           inSz = getSizeE inV
       forloop <- forUpToM inSz $ \ ix ->
                    SSet v (EIndexScalar inV (EVr ix)) :
                    stmts ++ -- This will consume v & w and write res.
                    [SSet w (EVr res)]
       -- The old arrayOpFvs are only for the kernel (the Lam) not for the extra bits that are
       -- parameters to the fold or are implicit.
       let newfvs = S.insert inV $
                    S.union (expFreeVars inSz) $
                    S.union (expFreeVars initE)
                            (S.fromList arrayOpFvs)
       ix2 <- genUnique
       let newop = Generate [one] $ Lam [(ix2,G.Default,TInt)] $
                   ScalarBlock ((v,G.Default,ty1) : (w,G.Default,ty2) : locals) [w] $
                     [SSet w initE,
                      forloop]
       rst <- doBinds sizeEnv prog rest 
       return (pb{ decor=(FreeVars$ S.toList newfvs), op = newop } : rst)
#endif
     GenReduce {} -> error$"DesugarFoldScan.hs: GenReduce did not match invariants for this pass: "++ show op

  where -- Goes with doBinds above.

    -- | Get an expression representing the size of an output array:
    getSizeE :: Var -> Exp
    getSizeE vr = 
      case M.lookup vr sizeEnv of 
        Just (_, TrivConst n)  -> EConst (I n)
        Just (_, TrivVarref v) -> EVr v
        Nothing -> error$"DesugarFoldScan.hs: no size entry for variable: "++show vr
               
--------------------------------------------------------------------------------

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

zero :: Exp
zero = EConst (I 0)

one :: Exp
one  = EConst (I 1)

-- Quadratic -- TODO: Use a Data.Map
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


mkScalarBind vr ty exp = do
  ignoredevt <- genUniqueWith "ignored"
  tmp        <- genUnique
  return$  GPUProgBind ignoredevt [] [(vr,Default,ty)] () 
                       (ScalarCode (ScalarBlock [(tmp,Default,ty)] [tmp] [SSet tmp exp])) 

fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a
