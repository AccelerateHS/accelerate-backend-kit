{-# LANGUAGE BangPatterns, GADTs, ScopedTypeVariables, CPP, TupleSections  #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- {-# ANN module "HLint: ignore Eta reduce" #-}

-- TODO LIST:
--   * Audit treatment of shapes and indices
--   * Audit tuple flattening guarantees
--   * Add type info to some language forms... 
--   * Convert boundary

#define SURFACE_TUPLES

module Data.Array.Accelerate.SimpleConverter 
       ( 
         convertToSimpleProg, 
         unpackArray, packArray, repackAcc, repackAcc2
       )
       where

-- standard libraries
import Control.Monad
import Control.Applicative ((<$>),(<*>))
import Prelude                                     hiding (sum)
import Control.Monad.State.Strict (State, evalState, runState, get, put, modify)
import Data.Map as M
import qualified Data.List as L
import Text.PrettyPrint.GenericPretty (Out(doc), Generic)

-- friends
import Data.Array.Accelerate.Type                  
import Data.Array.Accelerate.Array.Data            
import Data.Array.Accelerate.Array.Representation  hiding (sliceIndex)
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Tuple
-- import Data.Array.Accelerate.Analysis.Shape (accDim)
import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.SimpleArray as SA

import qualified Data.Array.Accelerate.SimpleAST   as S
-- Temporary AST before we get to the final one:
import qualified Data.Array.Accelerate.SimplePasses.IRTypes as T

import Data.Array.Accelerate.SimplePasses.Lowering (gatherLets, removeArrayTuple, liftComplexRands)

import Debug.Trace(trace)
tracePrint s x = trace (s ++ show x) x

dbg = True

--------------------------------------------------------------------------------
-- Exposed entrypoints for this module:
--------------------------------------------------------------------------------

-- | Convert the sophisticate Accelerate-internal AST representation
--   into something very simple for external consumption.
convertToSimpleProg :: Sug.Arrays a => Sug.Acc a -> S.Prog
convertToSimpleProg prog = 
  runPass "removeArrayTuple" removeArrayTuple $ 
  runPass "gatherLets"       gatherLets $  
  runPass "liftComplexRands" liftComplexRands $  
  runPass "initalConversion" (runEnvM . convertAcc . Sug.convertAcc) $ 
  prog

-- Pass composition:
runPass :: Out a => String -> (t -> a) -> t -> a
runPass msg pass input =
  if dbg then trace ("\n" ++ msg ++ ", output was:\n"++
                     "================================================================================\n"
                     ++ show (doc x)) x
         else x
 where x = pass input              

type TAExp = T.AExp S.Type

-- Temporary -- convert a Prog back to an AExp.  I haven't refactored
-- the interpreter yet....
-- progToAExp :: S.Prog -> TAExp
-- -- progToAExp = error "progToAExp UNFINISHED"
-- progToAExp (S.Letrec binds results finalty) = 
--   case ebinds of 
--     [] -> loop1 abinds
--     oth -> error $ "progToAExp: this function is not complete, can't handle these scalar bindings:\n"++show oth
--   where 
--     (ebinds, abinds) = L.partition isLeft binds
--     isLeft (_,_,Left _) = True
--     isLeft _            = False
--     loop1 [] = mkArrayTuple finalty $ zipWith T.Vr (deTupleTy finalty) results
--     loop1 ((vr,ty,Right rhs):tl) = T.Let finalty (vr,ty, T.reverseConvertAExps rhs) $ loop1 tl
--     deTupleTy (S.TTuple ls) = reverse ls
--     deTupleTy oth           = [oth]

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- We use a simple state monad for keeping track of the environment
type EnvM = State (SimpleEnv, Counter) 
type SimpleEnv = [S.Var]
type Counter = Int

runEnvM :: Num t => State ([a1], t) a -> a
runEnvM m = evalState m ([], 0)

-- Evaluate a sub-branch in an extended environment.
-- Returns the name of the fresh variable as well as the result:
withExtendedEnv :: String -> EnvM b -> EnvM (S.Var, b)
withExtendedEnv basename branch = do 
  (env,cnt) <- get 
  let newsym = S.var $ basename ++ show cnt
  put (newsym:env, cnt+1) 
  b <- branch
  -- We keep counter-increments from the sub-branch, but NOT the extended env:
  (_,cnt2) <- get 
  put (env,cnt2)
  return (newsym, b)

-- Look up a de bruijn index in the environment:
envLookup :: Int -> EnvM S.Var
envLookup i = do (env,_) <- get
                 if length env > i
                  then return (env !! i)
                  else error$ "Environment did not contain an element "++show i++" : "++show env

getAccType :: forall aenv ans . Sug.Arrays ans => OpenAcc aenv ans -> S.Type
getAccType _ = convertArrayType ty2 
  where 
      ty2 = Sug.arrays (typeOnlyErr "getAccType" :: ans) :: Sug.ArraysR (Sug.ArrRepr ans)

getAccTypePre :: Sug.Arrays ans => PreOpenAcc OpenAcc aenv ans -> S.Type
getAccTypePre acc = getAccType (OpenAcc acc)

getExpType :: forall env aenv ans . Sug.Elt ans => OpenExp env aenv ans -> S.Type
getExpType _ = convertType ty 
  where  ty  = Sug.eltType ((typeOnlyErr"getExpType")::ans) 

{-# INLINE typeOnlyErr #-}
typeOnlyErr msg = error$ msg++ ": This is a value that should never be evaluated.  It carries type information only."

--------------------------------------------------------------------------------
-- Convert Accelerate Array-level Expressions
--------------------------------------------------------------------------------

        
-- convertAcc :: Delayable a => OpenAcc aenv a -> EnvM T.AExp
convertAcc :: OpenAcc aenv a -> EnvM TAExp
convertAcc (OpenAcc cacc) = convertPreOpenAcc cacc 
 where 
 cvtSlice :: SliceIndex slix sl co dim -> S.SliceType
 cvtSlice (SliceNil)            = []
 cvtSlice (SliceAll   sliceIdx) = S.All   : cvtSlice sliceIdx 
 cvtSlice (SliceFixed sliceIdx) = S.Fixed : cvtSlice sliceIdx 

 convertPreOpenAcc :: forall aenv a . 
                      PreOpenAcc OpenAcc aenv a -> EnvM TAExp
 convertPreOpenAcc eacc = 
  let 
--    resty = getAccTypePre eacc 
    dummyty = S.TTuple []
  in
  case eacc of 
    Alet acc1 acc2 -> 
       do a1     <- convertAcc acc1
          (v,a2) <- withExtendedEnv "a"$ 
                    convertAcc acc2 
          let sty = getAccType acc1
          return$ T.Let (getAccTypePre eacc) (v,sty,a1) a2

    Avar idx -> 
      do var <- envLookup (idxToInt idx)
         return$ T.Vr (getAccTypePre eacc) var

    ------------------------------------------------------------
    -- Array creation:
    -- These should include types.
    
    Generate sh f -> T.Generate (getAccTypePre eacc)
                                <$> convertExp sh
                                <*> convertFun1 f

    -- This is real live runtime array data:
    Use (arrrepr :: Sug.ArrRepr a) ->
         -- This is rather odd, but we need to have a dummy return
         -- value to avoid errors about ArrRepr type functions not
         -- being injective.
         let (ty,arr,_::Phantom a) = unpackArray arrrepr in 
         return$ T.Use ty arr 

    -- End Array creation prims.
    ------------------------------------------------------------

    Acond cond acc1 acc2 -> T.Cond (getAccTypePre eacc)
                                   <$> convertExp cond 
                                   <*> convertAcc acc1 
                                   <*> convertAcc acc2

    Apply (Alam (Abody funAcc)) acc -> 
      do (v,bod) <- withExtendedEnv "a" $ convertAcc funAcc
         let sty = getAccType acc
         T.Apply (getAccTypePre eacc) (S.Lam1 (v, sty) bod) <$> convertAcc acc

    Apply _afun _acc -> error "convertAcc: This case is impossible"

    Atuple (atup :: Atuple (OpenAcc aenv) b ) -> 
      let loop :: Atuple (OpenAcc aenv') a' -> EnvM [TAExp] 
          loop NilAtup = return [] 
          loop (SnocAtup t a) = do first <- convertAcc a
                                   rest  <- loop t
                                   return (first : rest)
      in do ls <- loop atup
            return$ mkArrayTuple (getAccTypePre eacc) (reverse ls)

    Aprj ind expr -> 
      let len :: TupleIdx tr a -> Int 
          len ZeroTupIdx     = 0
          len (SuccTupIdx x) = 1 + len x
      in T.TupleRefFromRight (getAccTypePre eacc) (len ind) <$> convertAcc expr

    Unit e        -> T.Unit (getAccTypePre eacc) <$> convertExp e 

    Map     f acc       -> T.Map (getAccTypePre eacc) <$> convertFun1 f 
                                                      <*> convertAcc  acc
    ZipWith f acc1 acc2 -> T.ZipWith (getAccTypePre eacc)
                                     <$> convertFun2 f
                                     <*> convertAcc  acc1
                                     <*> convertAcc  acc2
    Fold     f e acc -> T.Fold  (getAccTypePre eacc)
                                <$> convertFun2 f
                                <*> convertExp  e 
                                <*> convertAcc  acc
    Fold1    f   acc -> T.Fold1 (getAccTypePre eacc)
                                <$> convertFun2 f
                                <*> convertAcc  acc
    FoldSeg  f e acc1 acc2 -> T.FoldSeg  (getAccTypePre eacc) 
                                         <$> convertFun2 f
                                         <*> convertExp  e
                                         <*> convertAcc  acc1
                                         <*> convertAcc  acc2
    Fold1Seg f   acc1 acc2 -> T.Fold1Seg (getAccTypePre eacc) 
                                         <$> convertFun2 f
                                         <*> convertAcc  acc1
                                         <*> convertAcc  acc2
    Scanl  f e acc -> T.Scanl  (getAccTypePre eacc)
                               <$> convertFun2 f
                               <*> convertExp  e 
                               <*> convertAcc  acc
    Scanl' f e acc -> T.Scanl' (getAccTypePre eacc)
                               <$> convertFun2 f
                               <*> convertExp  e 
                               <*> convertAcc  acc
    Scanl1 f   acc -> T.Scanl1 (getAccTypePre eacc)
                               <$> convertFun2 f
                               <*> convertAcc  acc
    Scanr  f e acc -> T.Scanr  (getAccTypePre eacc)
                               <$> convertFun2 f
                               <*> convertExp  e 
                               <*> convertAcc  acc
    Scanr' f e acc -> T.Scanr' (getAccTypePre eacc)
                               <$> convertFun2 f
                               <*> convertExp  e 
                               <*> convertAcc  acc
    Scanr1 f   acc -> T.Scanr1 (getAccTypePre eacc)
                               <$> convertFun2 f
                               <*> convertAcc  acc

    Replicate sliceIndex slix a ->
      T.Replicate (getAccTypePre eacc) 
                  (cvtSlice sliceIndex) 
                  <$> convertExp slix 
                  <*> convertAcc a
    Index sliceIndex acc slix -> 
      T.Index (getAccTypePre eacc) (cvtSlice sliceIndex) <$> convertAcc acc
                                          <*> convertExp slix
    Reshape e acc -> T.Reshape (getAccTypePre eacc) <$> convertExp e <*> convertAcc acc
    Permute fn dft pfn acc -> T.Permute (getAccType acc) -- Final type is same as input.
                                        <$> convertFun2 fn 
                                        <*> convertAcc  dft
                                        <*> convertFun1 pfn
                                        <*> convertAcc  acc
    Backpermute e pfn acc -> T.Backpermute (getAccTypePre eacc)
                                        <$> convertExp  e 
                                        <*> convertFun1 pfn
                                        <*> convertAcc  acc 
    Stencil  sten bndy acc -> T.Stencil (getAccTypePre eacc)
                                        <$> convertFun1 sten
                                        <*> return (convertBoundary bndy)
                                        <*> convertAcc acc
    Stencil2 sten bndy1 acc1 bndy2 acc2 -> 
      T.Stencil2 (getAccTypePre eacc)
                 <$> convertFun2 sten 
                 <*> return (convertBoundary bndy1) <*> convertAcc acc1
                 <*> return (convertBoundary bndy2) <*> convertAcc acc2



--------------------------------------------------------------------------------
-- Convert Accelerate Scalar Expressions
--------------------------------------------------------------------------------

-- For now I'm leaving it as an index from the right with no length:
convertTupleIdx :: TupleIdx t e -> Int
convertTupleIdx tix = loop tix
 where 
  loop :: TupleIdx t e -> Int
  loop ZeroTupIdx       = 0
  loop (SuccTupIdx idx) = 1 + loop idx

convertBoundary :: Boundary a -> S.Boundary
convertBoundary = error "convertBoundary: implement me" -- FIXME TODO

-- Evaluate a closed expression
convertExp :: forall env aenv ans . OpenExp env aenv ans -> EnvM T.Exp
convertExp e = 
  case e of 
    Let exp1 exp2 -> 
      do e1     <- convertExp exp1
         (v,e2) <- withExtendedEnv "e"$ 
                   convertExp exp2 
         let sty = getExpType exp1
         return$ T.ELet (v,sty,e1) e2
    
    -- Here is where we get to peek at the type of a variable:
    Var idx -> 
      do var <- envLookup (idxToInt idx)
         return$ T.EVr var
    
    -- Lift let's outside of primapps so we can get to the tuple:
    -- This will be tricky because of changing the debruijn indicies:
    -- PrimApp p (Let e1 e2) -> convertExp (Let e1 (PrimApp p e2))
    PrimApp p arg -> convertPrimApp p arg

    Tuple tup -> convertTuple tup

    Const c   -> return$ T.EConst$ 
                 convertConst (Sug.eltType (typeOnlyErr "convertExp" ::ans)) c

    -- NOTE: The incoming AST indexes tuples FROM THE RIGHT:
    Prj idx ex -> 
                 -- If I could get access to the IsTuple dict I could do something here:
                 -- The problem is the type function EltRepr....
                 let n = convertTupleIdx idx in 
--                 T.EPrj n m <$> convertExp e
                 T.ETupProjectFromRight n <$> convertExp ex

    -- This would seem to force indices to be LISTS at runtime??
    IndexNil       -> return$ T.EIndex []
    IndexCons esh ei -> do esh' <- convertExp esh
                           ei'  <- convertExp ei
                           return $ case esh' of
                             T.EIndex ls -> T.EIndex (ei' : ls)
                             _           -> T.EIndexConsDynamic ei' esh'
    IndexHead eix   -> do eix' <- convertExp eix
                          return $ case eix' of
                             -- WARNING: This is a potentially unsafe optimization:
                             -- Throwing away expressions:
                             T.EIndex (h:_) -> h 
                             T.EIndex []    -> error "IndexHead of empty index."
                             _              -> T.EIndexHeadDynamic eix'
    IndexTail eix   -> do eix' <- convertExp eix
                          return $ case eix' of
                             -- WARNING: This is a potentially unsafe optimization:
                             -- Throwing away expressions:
                             T.EIndex (_:tl) -> T.EIndex tl
                             T.EIndex []     -> error "IndexTail of empty index."
                             _               -> T.EIndexTailDynamic eix'
    IndexAny       -> error "convertToSimpleAST: not expecting to observe IndexAny value."
      -- return T.EIndexAny

    Cond c t ex -> T.ECond <$> convertExp c 
                           <*> convertExp t
                           <*> convertExp ex
    
    IndexScalar acc eix -> T.EIndexScalar <$> convertAcc acc
                                          <*> convertExp eix
    Shape acc -> T.EShape <$> convertAcc acc
    ShapeSize  acc -> T.EShapeSize  <$> convertExp acc

    -- We are committed to specific binary representations of numeric
    -- types anyway, so we simply encode special constants here,
    -- rather than preserving their specialness:
    PrimConst c -> return$ T.EConst $ 
                   case (c, getExpType e) of 
                     (PrimPi _, S.TFloat)   -> S.F pi 
                     (PrimPi _, S.TDouble)  -> S.D pi 
                     (PrimPi _, S.TCFloat)  -> S.CF pi 
                     (PrimPi _, S.TCDouble) -> S.CD pi 
                     (PrimMinBound _, S.TInt)    -> S.I   minBound
                     (PrimMinBound _, S.TInt8)   -> S.I8  minBound
                     (PrimMinBound _, S.TInt16)  -> S.I16 minBound
                     (PrimMinBound _, S.TInt32)  -> S.I32 minBound
                     (PrimMinBound _, S.TInt64)  -> S.I64 minBound
                     (PrimMinBound _, S.TWord)   -> S.W   minBound
                     (PrimMinBound _, S.TWord8)  -> S.W8  minBound
                     (PrimMinBound _, S.TWord16) -> S.W16 minBound
                     (PrimMinBound _, S.TWord32) -> S.W32 minBound
                     (PrimMinBound _, S.TWord64) -> S.W64 minBound
                     (PrimMinBound _, S.TCShort) -> S.CS  minBound
                     (PrimMinBound _, S.TCInt  ) -> S.CI  minBound
                     (PrimMinBound _, S.TCLong ) -> S.CL  minBound
                     (PrimMinBound _, S.TCLLong) -> S.CLL minBound
                     (PrimMinBound _, S.TCUShort) -> S.CUS  minBound
                     (PrimMinBound _, S.TCUInt  ) -> S.CUI  minBound
                     (PrimMinBound _, S.TCULong ) -> S.CUL  minBound
                     (PrimMinBound _, S.TCULLong) -> S.CULL minBound
                     (PrimMinBound _, S.TChar  )  -> S.C     minBound
                     (PrimMinBound _, S.TCChar )  -> S.CC    minBound
                     (PrimMinBound _, S.TCSChar)  -> S.CSC   minBound
                     (PrimMinBound _, S.TCUChar)  -> S.CUC   minBound
                     (PrimMaxBound _, S.TInt)    -> S.I   maxBound
                     (PrimMaxBound _, S.TInt8)   -> S.I8  maxBound
                     (PrimMaxBound _, S.TInt16)  -> S.I16 maxBound
                     (PrimMaxBound _, S.TInt32)  -> S.I32 maxBound
                     (PrimMaxBound _, S.TInt64)  -> S.I64 maxBound
                     (PrimMaxBound _, S.TWord)   -> S.W   maxBound
                     (PrimMaxBound _, S.TWord8)  -> S.W8  maxBound
                     (PrimMaxBound _, S.TWord16) -> S.W16 maxBound
                     (PrimMaxBound _, S.TWord32) -> S.W32 maxBound
                     (PrimMaxBound _, S.TWord64) -> S.W64 maxBound
                     (PrimMaxBound _, S.TCShort) -> S.CS  maxBound
                     (PrimMaxBound _, S.TCInt  ) -> S.CI  maxBound
                     (PrimMaxBound _, S.TCLong ) -> S.CL  maxBound
                     (PrimMaxBound _, S.TCLLong) -> S.CLL maxBound
                     (PrimMaxBound _, S.TCUShort) -> S.CUS  maxBound
                     (PrimMaxBound _, S.TCUInt  ) -> S.CUI  maxBound
                     (PrimMaxBound _, S.TCULong ) -> S.CUL  maxBound
                     (PrimMaxBound _, S.TCULLong) -> S.CULL maxBound
                     (PrimMaxBound _, S.TChar  )  -> S.C     maxBound
                     (PrimMaxBound _, S.TCChar )  -> S.CC    maxBound
                     (PrimMaxBound _, S.TCSChar)  -> S.CSC   maxBound
                     (PrimMaxBound _, S.TCUChar)  -> S.CUC   maxBound
                     (PrimMinBound _,ty) -> error$"Internal error: no minBound for type"++show ty
                     (PrimMaxBound _,ty) -> error$"Internal error: no maxBound for type"++show ty
                     (PrimPi       _,ty) -> error$"Internal error: no pi constant for type"++show ty


-- | Convert a tuple expression to our simpler Tuple representation (containing a list):
--   ASSUMES that the target expression is in fact a tuple construct.
#ifdef SURFACE_TUPLES                     
convertTuple :: Tuple (PreOpenExp OpenAcc env aenv) t' -> EnvM T.Exp
convertTuple NilTup = return$ T.ETuple []
convertTuple (SnocTup tup e) = 
    do e' <- convertExp e
       tup' <- convertTuple tup
       case tup' of 
         T.ETuple ls -> return$ T.ETuple$ ls ++ [e'] -- Snoc!
         se -> error$ "convertTuple: expected a tuple expression, received:\n  "++ show se
#else
-- Option 2: use a tupling that preservers the Acc-internal snoc-tree representation:
convertTuple :: Tuple (PreOpenExp OpenAcc env aenv) t' -> EnvM T.Exp
convertTuple NilTup = return$ T.ETuple []
convertTuple (SnocTup tup e) = 
    do e' <- convertExp e
       tup' <- convertTuple tup
       return (T.ETuple [tup', e'])
#endif

--------------------------------------------------------------------------------
-- Convert types
-------------------------------------------------------------------------------

convertType :: TupleType a -> S.Type
convertType ty = 
  tracePrint ("CONVERTTYPE of "++show ty++":  ") $
  tupleTy $ flattenTupTy $ 
  loop ty
 where   
  loop :: TupleType a -> S.Type
  loop ty =  
   case ty of 
     UnitTuple          -> S.TTuple []
     PairTuple ty1 ty0  -> S.TTuple [loop ty1, loop ty0] -- First, just extract the binary tree.
     SingleTuple scalar -> 
      case scalar of 
        NumScalarType (IntegralNumType typ) -> 
          case typ of 
            TypeInt   _  -> S.TInt
            TypeInt8  _  -> S.TInt8 
            TypeInt16 _  -> S.TInt16  
            TypeInt32 _  -> S.TInt32 
            TypeInt64 _  -> S.TInt64 
            TypeWord   _ -> S.TWord
            TypeWord8  _ -> S.TWord8 
            TypeWord16 _ -> S.TWord16 
            TypeWord32 _ -> S.TWord32 
            TypeWord64 _ -> S.TWord64 
            TypeCShort _ -> S.TCShort 
            TypeCInt   _ -> S.TCInt 
            TypeCLong  _ -> S.TCLong 
            TypeCLLong _ -> S.TCLLong 
            TypeCUShort _ -> S.TCUShort
            TypeCUInt   _ -> S.TCUInt
            TypeCULong  _ -> S.TCULong
            TypeCULLong _ -> S.TCULLong
        NumScalarType (FloatingNumType typ) -> 
          case typ of 
            TypeFloat _   -> S.TFloat 
            TypeDouble _  -> S.TDouble 
            TypeCFloat _  -> S.TCFloat 
            TypeCDouble _ -> S.TCDouble 
        NonNumScalarType typ -> 
          case typ of 
            TypeBool _   -> S.TBool 
            TypeChar _   -> S.TChar 
            TypeCChar _  -> S.TCChar 
            TypeCSChar _ -> S.TCSChar 
            TypeCUChar _ -> S.TCUChar 

-- | Convert a reified representation of an Accelerate (front-end)
--   array type into the simple representation.  By convention this
--   ignores the extra unit type at the end ((),arr).  
--           
--   That is, an array of ints will come out as just an array of ints
--   with no extra fuss.
convertArrayType :: forall arrs . Sug.ArraysR arrs -> S.Type
convertArrayType ty = 
#ifndef SURFACE_TUPLES
     removeOuterEndcap $ 
#endif
     tupleTy $ flattenTupTy $ loop ty
  where 
    loop :: forall arrs . Sug.ArraysR arrs -> S.Type
    loop ty = 
      case ty of 
       Sug.ArraysRunit  -> S.TTuple []
       -- Again, here we reify information from types (phantom type
       -- parameters) into a concrete data-representation:
       Sug.ArraysRarray | (_ :: Sug.ArraysR (Sug.Array sh e)) <- ty -> 
          let ety = Sug.eltType ((error"This shouldn't happen (3)")::e) in
          S.TArray (Sug.dim (Sug.ignore :: sh)) (convertType ety)          
                                                 
       Sug.ArraysRpair t0 t1 -> S.TTuple [loop t0, loop t1]

-- Flatten the snoc-list representation of tuples, at the array as well as scalar level
flattenTupTy :: S.Type -> [S.Type]
flattenTupTy ty = 
#ifdef SURFACE_TUPLES
  -- reverse $ 
  loop ty 
 where 
  -- When using the surface representation we reverse (cons instead of snoc):
  mkTup = S.TTuple -- . reverse
#else
  -- DISABLE flattening  
  case ty of
    S.TTuple ls -> ls
    oth         -> [oth]
 where 
  mkTup = S.TTuple 
#endif
  isClosed (S.TTuple [])    = True
  isClosed (S.TTuple [l,r]) = isClosed l
  isClosed _                = False
  loop (S.TTuple [])        = []
  -- isClosed means 'left' is a standalone tuple and 'right' does not extend it:
  loop (S.TTuple [left,right]) | isClosed right = [mkTup [tupleTy (loop left), tupleTy (loop right)]]
--                               | otherwise      =  tupleTy (loop right) : loop left
                               | otherwise      =  loop left ++ [tupleTy (loop right)]
  loop (S.TTuple ls) = error$"flattenTupTy: expecting binary-tree tuples as input, recieved: "++show(S.TTuple ls)
  loop oth           = [oth]

removeOuterEndcap (S.TTuple [S.TTuple [], ty]) = ty
removeOuterEndcap oth                          = oth

tupleTy [ty] = ty
tupleTy ls = S.TTuple ls


--------------------------------------------------------------------------------
-- Convert constants    
-------------------------------------------------------------------------------

-- convertConst :: Sug.Elt t => Sug.EltRepr t -> S.Const
convertConst :: TupleType a -> a -> S.Const
convertConst ty c = 
--  tracePrint "Converting tuple const: " $
  case ty of 
    UnitTuple -> S.Tup []
    PairTuple ty1 ty0 -> let (c1,c0) = c 
                             c0' = convertConst ty0 c0
                         in 
                         case convertConst ty1 c1 of
                           S.Tup [] -> c0' 
                           S.Tup ls -> S.Tup (c0' : ls)
                           singl -> S.Tup [c0', singl]
--                           oth -> error$ "mal constructed tuple on RHS of PairTuple: "++ show oth
    SingleTuple scalar -> 
      case scalar of 
        NumScalarType (IntegralNumType typ) -> 
          case typ of 
            TypeInt   _  -> S.I  c
            TypeInt8  _  -> S.I8  c
            TypeInt16 _  -> S.I16 c
            TypeInt32 _  -> S.I32 c
            TypeInt64 _  -> S.I64 c
            TypeWord   _ -> S.W  c
            TypeWord8  _ -> S.W8  c
            TypeWord16 _ -> S.W16 c
            TypeWord32 _ -> S.W32 c
            TypeWord64 _ -> S.W64 c
            TypeCShort _ -> S.CS  c
            TypeCInt   _ -> S.CI  c
            TypeCLong  _ -> S.CL  c
            TypeCLLong _ -> S.CLL c
            TypeCUShort _ -> S.CUS  c
            TypeCUInt   _ -> S.CUI  c
            TypeCULong  _ -> S.CUL  c
            TypeCULLong _ -> S.CULL c
        NumScalarType (FloatingNumType typ) -> 
          case typ of 
            TypeFloat _   -> S.F c    
            TypeDouble _  -> S.D c 
            TypeCFloat _  -> S.CF c    
            TypeCDouble _ -> S.CD c 
        NonNumScalarType typ -> 
          case typ of 
            TypeBool _   -> S.B c
            TypeChar _   -> S.C c
            TypeCChar _  -> S.CC c
            TypeCSChar _ -> S.CSC c 
            TypeCUChar _ -> S.CUC c

--------------------------------------------------------------------------------
-- Convert Accelerate Primitive Applications: 
--------------------------------------------------------------------------------

convertPrimApp :: forall a b env aenv . (Sug.Elt a, Sug.Elt b)
               => PrimFun (a -> b) -> PreOpenExp OpenAcc env aenv a
               -> EnvM T.Exp               
convertPrimApp p arg = 
  do 
     args2 <- convertExp arg
     return (loop args2)
 where 
   -- ASSUMPTION!  We assume that there is nothing keeping the primapp
   -- from its args except for Lets...
   loop :: T.Exp -> T.Exp
   -- Push primapps inside lets:
   loop args' = case args' of 
                  T.ELet (v,sty,e1) e2 ->
                    T.ELet (v,sty,e1) (loop e2)
                  -- WARNING!  Need a sanity check on arity here:
                  T.ETuple ls -> mkPapp ls
                  oth         -> mkPapp [oth]
                  
   ty = getExpType (error "convertPrimApp: dummy value should not be used" :: OpenExp env aenv b)
   mkPapp ls = if length ls == arity
               then T.EPrimApp ty newprim ls
               else error$"SimpleConverter.convertPrimApp: wrong number of arguments to prim "
                    ++show newprim++": "++ show ls
   arity   = S.primArity newprim
   newprim = op p 
   op pr   = 
    case pr of 
      PrimAdd _ty -> S.NP S.Add
      PrimSub _ty -> S.NP S.Sub
      PrimMul _ty -> S.NP S.Mul
      PrimSig _ty -> S.NP S.Sig
      PrimAbs _ty -> S.NP S.Abs
      PrimNeg _ty -> S.NP S.Neg
      
      PrimQuot _ty -> S.IP S.Quot
      PrimRem  _   -> S.IP S.Rem
      PrimIDiv _   -> S.IP S.IDiv
      PrimMod  _   -> S.IP S.Mod
      PrimBAnd _   -> S.IP S.BAnd
      PrimBOr  _   -> S.IP S.BOr
      PrimBXor _   -> S.IP S.BXor
      PrimBNot _   -> S.IP S.BNot
      PrimBShiftL _ -> S.IP S.BShiftL
      PrimBShiftR _ -> S.IP S.BShiftR
      PrimBRotateL _ -> S.IP S.BRotateL
      PrimBRotateR _ -> S.IP S.BRotateR
  
      PrimFDiv  _ -> S.FP S.FDiv
      PrimRecip _ -> S.FP S.Recip
      PrimSin   _ -> S.FP S.Sin
      PrimCos   _ -> S.FP S.Cos
      PrimTan   _ -> S.FP S.Tan
      PrimAsin  _ -> S.FP S.Asin
      PrimAcos  _ -> S.FP S.Acos
      PrimAtan  _ -> S.FP S.Atan
      PrimAsinh _ -> S.FP S.Asinh
      PrimAcosh _ -> S.FP S.Acosh
      PrimAtanh _ -> S.FP S.Atanh
      PrimExpFloating _ -> S.FP S.ExpFloating
      PrimSqrt _ -> S.FP S.Sqrt
      PrimLog  _ -> S.FP S.Log
      PrimFPow _ -> S.FP S.FPow
      PrimLogBase _ -> S.FP S.LogBase
      PrimAtan2   _ -> S.FP S.Atan2
      PrimTruncate _ _ -> S.FP S.Truncate
      PrimRound  _ _ -> S.FP S.Round
      PrimFloor  _ _ -> S.FP S.Floor
      PrimCeiling _ _ -> S.FP S.Ceiling
      
      PrimLt   _ -> S.SP S.Lt
      PrimGt   _ -> S.SP S.Gt
      PrimLtEq _ -> S.SP S.LtEq
      PrimGtEq _ -> S.SP S.GtEq
      PrimEq  _  -> S.SP S.Eq
      PrimNEq _  -> S.SP S.NEq
      PrimMax _  -> S.SP S.Max
      PrimMin _  -> S.SP S.Min

      PrimLAnd  -> S.BP S.And
      PrimLOr   -> S.BP S.Or
      PrimLNot  -> S.BP S.Not

      PrimOrd   -> S.OP S.Ord
      PrimChr   -> S.OP S.Chr

      PrimBoolToInt      -> S.OP S.BoolToInt
      PrimFromIntegral _ _ -> S.OP S.FromIntegral


--------------------------------------------------------------------------------
-- Convert Accelerate Functions
--------------------------------------------------------------------------------

-- Convert an open, scalar function with arbitrary arity:
convertFun :: OpenFun e ae t0 -> EnvM ([(S.Var,S.Type)],T.Exp)
convertFun =  loop [] 
 where 
   loop :: forall env aenv t . 
           [(S.Var,S.Type)] -> OpenFun env aenv t -> EnvM ([(S.Var,S.Type)],T.Exp)
   loop acc (Body b) = do b'  <- convertExp b 
                          -- It would perhaps be nice to record the output type of function 
                          -- here as well.  But b's type isn't in class Elt.
                          return (reverse acc, b')
   -- Here we again dig around in the Haskell types to find the type information we need.
   -- In this case we use quite a few scoped type variables:
   loop acc orig@(Lam f2) | (_:: OpenFun env aenv (arg -> res)) <- orig 
                          = do 
                               let (_:: OpenFun (env, arg) aenv res) = f2 
                                   ety = Sug.eltType ((error"This shouldn't happen (4)") :: arg)
                                   sty = convertType ety
                               (_,x) <- withExtendedEnv "v" $ do
                                          v <- envLookup 0
                                          loop ((v,sty) : acc) f2
                               return x 

convertFun1 :: OpenFun e ae t0 -> EnvM (S.Fun1 T.Exp)
convertFun1 fn = do 
  x <- convertFun fn
  case x of 
    ([(v,ty)], bod) -> return$ S.Lam1 (v,ty) bod
    (ls,_) -> error$"convertFun1: expected Accelerate function of arity one, instead arguments were: "++show ls

convertFun2 :: OpenFun e ae t0 -> EnvM (S.Fun2 T.Exp)
convertFun2 fn = do
  x <- convertFun fn
  case x of 
    ([(v1,ty1),(v2,ty2)], bod) -> return$ S.Lam2 (v1,ty1) (v2,ty2) bod
    (ls,_) -> error$"convertFun2: expected Accelerate function of arity two, instead arguments were: "++show ls



--------------------------------------------------------------------------------
-- Convert Accelerate Array Data
--------------------------------------------------------------------------------

-- | Used only for communicating type information.
data Phantom a = Phantom

-- | This converts Accelerate Array data.  It has an odd return type
--   to avoid type-family related type errors.
unpackArray :: forall a . (Sug.Arrays a) => Sug.ArrRepr a -> (S.Type, S.AccArray, Phantom a)
unpackArray arrrepr = (ty, S.AccArray shp payloads, 
                        Phantom :: Phantom a)
  where 
   shp = case L.group shps of
           [] -> []
           [(hd : _gr1)] -> hd
           ls -> error$"Use: corrupt Accelerate array -- arrays components did not have identical shape:"
                 ++ show (concat ls)
   (shps, payloads)  = cvt2 repOf actualArr
   ty        = convertArrayType repOf
   repOf     = Sug.arrays actualArr  :: Sug.ArraysR (Sug.ArrRepr a)
   actualArr = Sug.toArr  arrrepr    :: a   

   -- cvt and cvt2 return a list of shapes together with a list of raw data payloads.
   -- 
   -- I'm afraid I don't understand the two-level pairing that
   -- is going on here (ArraysRpair + ArraysEltRpair)
   cvt :: Sug.ArraysR a' -> a' -> ([[Int]],[S.ArrayPayload])
   cvt Sug.ArraysRunit         ()       = ([],[])
   cvt (Sug.ArraysRpair r1 r2) (a1, a2) = cvt r1 a1 `combine` cvt r2 a2
   cvt Sug.ArraysRarray  arr            = cvt3 arr

   -- Takes an Array representation and its reified type:
   cvt2 :: (Sug.Arrays a') => Sug.ArraysR (Sug.ArrRepr a') -> a' -> ([[Int]],[S.ArrayPayload])
   cvt2 tyReified arr = 
     case (tyReified, Sug.fromArr arr) of 
       (Sug.ArraysRunit, ()) -> ([],[])
       (Sug.ArraysRpair r1 r2, (a1, a2)) -> cvt r1 a1 `combine` cvt r2 a2
       (Sug.ArraysRarray, arr2)          -> cvt3 arr2

   combine (a,b) (x,y) = (a++x, b++y)

   cvt3 :: forall dim e . (Sug.Elt e) => Sug.Array dim e -> ([[Int]],[S.ArrayPayload])
   cvt3 (Sug.Array shpVal adata) = 
        ([Sug.shapeToList (Sug.toElt shpVal :: dim)], 
         useR arrayElt adata)
     where 
       -- This [mandatory] type signature forces the array data to be the
       -- same type as the ArrayElt Representation (elt ~ elt):
       useR :: ArrayEltR elt -> ArrayData elt -> [S.ArrayPayload]
       useR (ArrayEltRpair aeR1 aeR2) ad = 
         (useR aeR1 (fstArrayData ad)) ++ 
         (useR aeR2 (sndArrayData ad))
   --             useR ArrayEltRunit             _   = [S.ArrayPayloadUnit]
       useR ArrayEltRunit             _   = []
       useR ArrayEltRint    (AD_Int   x)  = [S.ArrayPayloadInt   x]
       useR ArrayEltRint8   (AD_Int8  x)  = [S.ArrayPayloadInt8  x]
       useR ArrayEltRint16  (AD_Int16 x)  = [S.ArrayPayloadInt16 x]
       useR ArrayEltRint32  (AD_Int32 x)  = [S.ArrayPayloadInt32 x]
       useR ArrayEltRint64  (AD_Int64 x)  = [S.ArrayPayloadInt64 x]
       useR ArrayEltRword   (AD_Word   x) = [S.ArrayPayloadWord   x]
       useR ArrayEltRword8  (AD_Word8  x) = [S.ArrayPayloadWord8  x]
       useR ArrayEltRword16 (AD_Word16 x) = [S.ArrayPayloadWord16 x]
       useR ArrayEltRword32 (AD_Word32 x) = [S.ArrayPayloadWord32 x]
       useR ArrayEltRword64 (AD_Word64 x) = [S.ArrayPayloadWord64 x]            
       useR ArrayEltRfloat  (AD_Float  x) = [S.ArrayPayloadFloat  x]
       useR ArrayEltRdouble (AD_Double x) = [S.ArrayPayloadDouble x]
       useR ArrayEltRbool   (AD_Bool   x) = [S.ArrayPayloadBool   x]
       useR ArrayEltRchar   (AD_Char   x) = [S.ArrayPayloadChar   x]            


-- | Almost an inverse of the previous function -- repack the simplified data
-- representation with the type information necessary to form a proper
-- Accelerate array.
packArray :: forall sh e . (Sug.Elt e, Sug.Shape sh) => S.AccArray -> Sug.Array sh e

-- packArray (S.AccArray dims []) = 
--   if all (== 0) dims
--   then Sug.Array (Sug.fromElt (Sug.listToShape dims :: sh)) (error "UNFINISHED: packArray")
--   else error$ "packArray: corrupt input AccArray is empty, but stated dimensions are: "++ show dims

packArray orig@(S.AccArray dims payloads) = 
  if length dims == length dims' -- Is the expected rank correct?
  then Sug.Array shpVal (packit (typeOnlyErr "packArray1"::Sug.Array sh e) payloads)
  else error$"SimpleConverter.packArray: array does not have the expected dimensions: "++show dims++" expected "++show dims'
 where 
  shpVal :: Sug.EltRepr sh = Sug.fromElt (Sug.listToShape dims :: sh)
  dims' :: [Int] = Sug.shapeToList (Sug.ignore::sh)

  packit :: forall sh e . (Sug.Shape sh, Sug.Elt e) => Sug.Array sh e -> [S.ArrayPayload] -> (ArrayData (Sug.EltRepr e))
  packit _ pays = loop eTy pays
     where eTy = Sug.eltType (typeOnlyErr"packArray2"::e) 

  loop :: forall e . TupleType e -> [S.ArrayPayload] -> (ArrayData e)
  loop tupTy payloads =
--   trace ("LOOPING "++show (length payloads)++" tupty:"++show tupTy) $
   let err2 :: String -> (forall a . a)
       err2 msg = error$"packArray: given a SimpleAST.AccArray of the wrong type, expected "++msg
                  ++" received "++ show(length payloads) ++ " payloads: "++paystr
       paystr = "\n"++(unlines$ L.map (take 200 . show) payloads) ++ "\n dimension: "++show dims
   in
   case (tupTy, payloads) of
    (UnitTuple,_)     -> AD_Unit

    -- Tuples are nested ON THE LEFT in Accelerate currently:
    -- In SimpleAST we ignore the extra unit on the end in the AccArray representation:
    (PairTuple UnitTuple (r::TupleType b),_)  -> AD_Pair AD_Unit (loop r payloads) 
    -- This might occur given our representation of `All` in slice descriptors:
    -- But these units DON'T have a physical representation in the payloads:
    (PairTuple (r::TupleType b) UnitTuple, _) -> AD_Pair (loop r payloads) AD_Unit 
    (PairTuple t1 t2, ls)  -> AD_Pair (loop t1 (init ls)) (loop t2 [last ls])

    (SingleTuple (NumScalarType (FloatingNumType (TypeFloat _))),  [S.ArrayPayloadFloat uarr])  -> AD_Float uarr
    (SingleTuple (NumScalarType (FloatingNumType (TypeDouble _))), [S.ArrayPayloadDouble uarr]) -> AD_Double uarr

    (SingleTuple (NumScalarType (IntegralNumType (TypeInt   _))), [S.ArrayPayloadInt   uarr]) -> AD_Int uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt8  _))), [S.ArrayPayloadInt8  uarr]) -> AD_Int8 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt16 _))), [S.ArrayPayloadInt16 uarr]) -> AD_Int16 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt32 _))), [S.ArrayPayloadInt32 uarr]) -> AD_Int32 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt64 _))), [S.ArrayPayloadInt64 uarr]) -> AD_Int64 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord   _))), [S.ArrayPayloadWord   uarr]) -> AD_Word uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord8  _))), [S.ArrayPayloadWord8  uarr]) -> AD_Word8 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord16 _))), [S.ArrayPayloadWord16 uarr]) -> AD_Word16 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord32 _))), [S.ArrayPayloadWord32 uarr]) -> AD_Word32 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord64 _))), [S.ArrayPayloadWord64 uarr]) -> AD_Word64 uarr

    (SingleTuple (NonNumScalarType (TypeBool _)), [S.ArrayPayloadBool uarr]) -> AD_Bool uarr
    (SingleTuple (NonNumScalarType (TypeChar _)), [S.ArrayPayloadChar uarr]) -> AD_Char uarr

    (SingleTuple (NumScalarType (FloatingNumType (TypeCFloat _))),  _)  -> error "not supported yet: array of CFloat"
    (SingleTuple (NumScalarType (FloatingNumType (TypeCDouble _))), _)  -> error "not supported yet: array of CDouble"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCShort   _))), _) -> error "not supported yet: array of CShort"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCUShort  _))), _) -> error "not supported yet: array of CUShort"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCInt    _))), _)  -> error "not supported yet: array of CInt"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCUInt _))), _)    -> error "not supported yet: array of CUInt"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCLong _))), _)    -> error "not supported yet: array of CLong"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCULong _))), _)   -> error "not supported yet: array of CULong"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCLLong _))), _)   -> error "not supported yet: array of CLLong"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCULLong _))), _)  -> error "not supported yet: array of CULLong"
    (SingleTuple (NonNumScalarType (TypeCChar _)), _)  -> error "not supported yet: array of CChar"
    (SingleTuple (NonNumScalarType (TypeCSChar _)), _) -> error "not supported yet: array of CSChar"
    (SingleTuple (NonNumScalarType (TypeCUChar _)), _) -> error "not supported yet: array of CUChar"

    -- We could have a single catch-all cases here, but blowing it up
    -- like this allows meaningful feedback from -fwarn-incomplete-patterns:
    (SingleTuple (NumScalarType (FloatingNumType (TypeFloat _))),  _) -> err2 "Float"
    (SingleTuple (NumScalarType (FloatingNumType (TypeDouble _))), _) -> err2 "Double"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt   _))), _) -> err2 "Int"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt8  _))), _) -> err2 "Int8"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt16 _))), _) -> err2 "Int16"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt32 _))), _) -> err2 "Int32"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt64 _))), _) -> err2 "Int64"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord   _))), _) -> err2 "Word"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord8  _))), _) -> err2 "Word8"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord16 _))), _) -> err2 "Word16"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord32 _))), _) -> err2 "Word32"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord64 _))), _) -> err2 "Word64"
    (SingleTuple (NonNumScalarType (TypeBool _)), _) -> err2 "Bool"
    (SingleTuple (NonNumScalarType (TypeChar _)), _) -> err2  "Char"
  


-- | Repackage a result in simplified form as an properly-typed result
--   of an Acc computation, i.e. a real Accelerate array.
repackAcc :: forall a . Sug.Arrays a 
        => {- dummy -} Sug.Acc a -> S.AccArray -> a
repackAcc dummy simpl = Sug.toArr converted
  where
   converted :: Sug.ArrRepr a = cvt rep simpl 
   -- Pull some information out of thin air (from type domain to value domain):
   rep :: Sug.ArraysR (Sug.ArrRepr a) = 
     Sug.arrays (error"SimpleInterp.run: this should never be used" :: a)

   cvt :: forall a' . Sug.ArraysR a' -> S.AccArray -> a'
   cvt arrR simpl = 
     case arrR of 
       Sug.ArraysRunit       -> ()
       -- We don't explicitly represent this extra capstone-unit in the AccArray:
       Sug.ArraysRpair Sug.ArraysRunit r -> ((), cvt r simpl)
       Sug.ArraysRpair r1 r2 -> let (a1,a2) = SA.splitComponent simpl in 
                                (cvt r1 a1, cvt r2 a2)
       Sug.ArraysRarray | (_ :: Sug.ArraysR (Sug.Array sh e)) <- arrR ->
         (packArray simpl) :: (Sug.Array sh e)

-- | Repackage a result in simplified form as an properly-typed result
--   of an Acc computation, i.e. a real Accelerate array.
repackAcc2 :: forall a . Sug.Arrays a 
        => {- dummy -} Sug.Acc a -> [S.AccArray] -> a
repackAcc2 dummy simpls = 
      trace ("repackAcc2: ... "++show rep++", given "++show (length simpls)++" arrs:\n"
              ++ unlines(L.map (("   "++) . show) simpls)) $ 
      Sug.toArr converted
  where
   converted :: Sug.ArrRepr a = fst$ cvt rep (reverse simpls)
   -- Pull some information out of thin air (from type domain to value domain):
   rep :: Sug.ArraysR (Sug.ArrRepr a) = 
     Sug.arrays (error"SimpleInterp.run: this should never be used" :: a)

   -- In additon to a result, returns unused input arrays:
   cvt :: forall a' . Sug.ArraysR a' -> [S.AccArray] -> (a',[S.AccArray])
   cvt arrR simpls = 
     case arrR of 
       Sug.ArraysRunit       -> ((),simpls)
       -- We don't explicitly represent this extra capstone-unit in the AccArray:
       Sug.ArraysRpair Sug.ArraysRunit r -> 
           let (res,rst) = cvt r simpls in
           (((), res), rst)
       Sug.ArraysRpair r1 r2 -> 
           -- Dole out the available input arrays to cover the
           -- leaves, filling in the right first:
           let (res2,rst)  = cvt r2 simpls 
               (res1,rst') = cvt r1 rst
           in ((res1,res2), rst')
       Sug.ArraysRarray | (_ :: Sug.ArraysR (Sug.Array sh e)) <- arrR ->
         case simpls of 
           hd:tl -> ((packArray hd) :: (Sug.Array sh e), tl)
           oth  -> error$"repackAcc2: ran out of input arrays.\n"

instance Show (Sug.ArraysR a') where
  show arrR = "ArraysR "++loop arrR
   where 
    loop :: forall ar .  Sug.ArraysR ar -> String
    loop arrR =  
     case arrR of 
       Sug.ArraysRunit       -> "()"
--       Sug.ArraysRpair Sug.ArraysRunit r -> "(() "++loop r ++")"
       Sug.ArraysRpair r1 r2 -> "("++ loop r1 ++", "++ loop r2++")"
       Sug.ArraysRarray -> "Array"

mkArrayTuple ty [one] = one
mkArrayTuple ty ls    = T.ArrayTuple ty ls

--------------------------------------------------------------------------------

