{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- {-# ANN module "HLint: ignore Eta reduce" #-}

-- TODO LIST:
--   * Audit treatment of shapes and indices
--   * Audit tuple flattening guarantees
--   * Add type info to some language forms...
--   * Convert boundary

-- | PHASE1 :  Accelerate -> SimpleAcc
--
-- This module provides a function to convert from Accelerate's
-- internal representation to the `SimpleAcc` external representation.
-- This representation retains nearly the full set of Accelerate
-- language constructs.  Desugaring is postponed to phase 2.
module Data.Array.Accelerate.BackendKit.Phase1.ToAccClone
       (
         accToAccClone, expToExpClone,
         expType, convertSliceIndex,
         unpackArray, packArray, repackAcc, Phantom(Phantom),

         convertEltType, convertArrayType,
       )
       where

-- standard libraries:
import           Control.Monad
import           Control.Applicative        ((<$>),(<*>))
import           Prelude                    hiding (sum)
import           Control.Monad.State.Strict (State, evalState, runState, get, put, modify)
import           Debug.Trace                (trace)
import           Data.Map  as M
import qualified Data.List as L
import           Text.PrettyPrint.GenericPretty (Out(doc), Generic)

-- friends:
import           Data.Array.Accelerate.Type
import           Data.Array.Accelerate.Array.Data
import           Data.Array.Accelerate.Array.Representation  hiding (sliceIndex)
import qualified Data.Array.Accelerate.Analysis.Type as Sug 
import           Data.Array.Accelerate.AST         as AST
import           Data.Array.Accelerate.Tuple
import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.Trafo.Sharing as Cvt
import qualified Data.Array.Accelerate.BackendKit.SimpleArray as SA
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (maybtrace, Phantom(..))
  -- Temporary AST before we get to the final one:
import qualified Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone as T

--------------------------------------------------------------------------------
-- Main entrypoint
--------------------------------------------------------------------------------

-- | Convert from the internal Acc representation to the temporary
-- (isomorphic) `AccClone` representation.
accToAccClone :: Sug.Arrays a => AST.Acc a -> TAExp
accToAccClone = runEnvM . convertAcc

-- | Must take a closed expression.
-- expToExpClone :: forall env aenv ans . OpenExp env aenv ans -> T.Exp
expToExpClone :: AST.Exp () ans -> T.Exp
expToExpClone x = runEnvM (convertExp x)

-- | Reify the type of an expression in our plain format.
expType :: (Sug.Elt ans) => AST.Exp () ans -> S.Type
expType = getExpType

-- type OpenExp = PreOpenExp OpenAcc
-- type Exp = OpenExp () = PreOpenExp OpenAcc ()
-- data PreOpenExp (acc :: * -> * -> *) env aenv t where


type TAExp = T.AExp S.Type

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- | We use a simple state monad for keeping track of the environment (and resolving
-- De-bruijn indices).  Following the Accelerate front-end conventions, we use
-- separate environments for scalar and array bindings.
type EnvM = State (SimpleEnv, Counter)
type Counter = Int
data SimpleEnv = SimpleEnv { scalarEnv :: [S.Var],
                             arrayEnv  :: [S.Var] }
  deriving (Show)


runEnvM :: Num t => State (SimpleEnv, t) a -> a
runEnvM m = evalState m (SimpleEnv [] [], 0)

-- | Evaluate a sub-branch in an extended SCALAR environment.
--   Returns the name of the fresh variable as well as the result:
withExtendedScalarEnv :: String -> EnvM b -> EnvM (S.Var, b)
withExtendedScalarEnv basename branch = do
  (orig@(SimpleEnv env aenv),cnt) <- get

  -- FIXME: use the genUnique library routine:
  let newsym = S.var $ basename ++ show cnt
  put (SimpleEnv (newsym:env) aenv, cnt+1)
  b <- branch
  -- We keep counter-increments from the sub-branch, but NOT the extended env:
  (_,cnt2) <- get
  put (orig,cnt2)
  return (newsym, b)

-- | Look up a de bruijn index in the SCALAR environment to find the variables new name.
envLookupScalar :: Int -> EnvM S.Var
envLookupScalar i =
  do (SimpleEnv env _,_) <- get
     if length env > i
       then return (env !! i)
       else error$ "Environment did not contain an element "++show i++" : "++show env

-- | Ditto for arrays.
withExtendedArrayEnv :: String -> EnvM b -> EnvM (S.Var, b)
withExtendedArrayEnv basename branch = do
  (orig@(SimpleEnv env aenv),cnt) <- get
  let newsym = S.var $ basename ++ show cnt
  put (SimpleEnv env (newsym:aenv), cnt+1)
  b <- branch
  -- We keep counter-increments from the sub-branch, but NOT the extended env:
  (_,cnt2) <- get
  put (orig,cnt2)
  return (newsym, b)


-- | Ditto for arrays.
envLookupArray :: Int -> EnvM S.Var
envLookupArray i =
  do (SimpleEnv _ aenv,_) <- get
     if length aenv > i
       then return (aenv !! i)
       else error$ "Environment did not contain an element "++show i++" : "++show aenv

--------------------------------------------------------------------------------

getAccType :: forall aenv arrs . Sug.Arrays arrs => OpenAcc aenv arrs -> S.Type
getAccType _ =
  maybtrace (" [ToAccClone] getAccType: "++show accType++"\n  -> "++show simpleType) simpleType
  where
    simpleType  = convertArrayType (undefined :: arrs)
    accType     = Sug.arrays (typeOnlyErr "getAccType" :: arrs) :: Sug.ArraysR (Sug.ArrRepr arrs)

getAccTypePre :: Sug.Arrays arrs => PreOpenAcc OpenAcc aenv arrs -> S.Type
getAccTypePre acc =
   getAccType (OpenAcc acc)

getExpType :: forall env aenv t . Sug.Elt t => OpenExp env aenv t -> S.Type
getExpType _ = convertEltType (undefined :: t)

{-# INLINE typeOnlyErr #-}
typeOnlyErr msg = error$ msg++ ": This is a value that should never be evaluated.  It carries type information only."

--------------------------------------------------------------------------------
-- Convert Accelerate Array-level Expressions
--------------------------------------------------------------------------------


-- convertAcc :: Delayable a => OpenAcc aenv a -> EnvM T.AExp
convertAcc :: OpenAcc aenv a -> EnvM TAExp
convertAcc (OpenAcc cacc) =
  convertPreOpenAcc cacc
 where
 convertPreOpenAcc :: forall aenv a .
                      PreOpenAcc OpenAcc aenv a -> EnvM TAExp
 convertPreOpenAcc eacc =
  let
--    resty = getAccTypePre eacc
    dummyty = S.TTuple []
  in
  case eacc of
--     _ -> error "FINISHME -- fix a GHC 7.8 only type error"


    Alet acc1 acc2 ->
       do a1     <- convertAcc acc1
          (v,a2) <- withExtendedArrayEnv "aLt"$
                    convertAcc acc2
          let sty = getAccType acc1
          return$ T.Let (getAccTypePre eacc) (v,sty,a1) a2

    Avar idx ->
      do var <- envLookupArray (idxToInt idx)
         return$ T.Vr (getAccTypePre eacc) var

    ------------------------------------------------------------
    -- Array creation:
    -- These should include types.

    Generate sh f -> T.Generate (getAccTypePre eacc)
                                <$> convertExp sh
                                <*> convertFun1 f

    -- This is real live runtime array data:
    -- Handle tuples of arrays by 'unrolling' a single Use into many.
    -- mkArrayTuple fixes the case where there was only one array by [one] -> one case.
    --
    Use (arrs :: Sug.ArrRepr a) ->
      let arrs' = L.map (\a -> T.Use (S.arrType a) a) $ unpackArray (Sug.toArr arrs :: a)
          ty    = getAccTypePre eacc
      in
      return $ mkArrayTuple ty arrs'

    -- End Array creation prims.
    ------------------------------------------------------------

    Acond cond acc1 acc2 -> T.Cond (getAccTypePre eacc)
                                   <$> convertExp cond
                                   <*> convertAcc acc1
                                   <*> convertAcc acc2

    Apply (Alam (Abody funAcc)) acc ->
      do (v,bod) <- withExtendedArrayEnv "aAp" $ convertAcc funAcc
         let sty = getAccType acc
         T.Apply (getAccTypePre eacc) (S.Lam1 (v, sty) bod) <$> convertAcc acc

    Apply _afun _acc -> error "convertAcc: This case is impossible"

    Atuple (atup :: Atuple (OpenAcc aenv) (TupleRepr a) ) ->
      let loop :: Atuple (OpenAcc aenv') a' -> EnvM [TAExp]
          loop NilAtup = return []
          loop (SnocAtup t a) = do first <- convertAcc a
                                   rest  <- loop t
                                   return (first : rest)
      in do ls <- loop atup
            return$ mkArrayTuple (getAccTypePre eacc) (reverse ls)

    -- Aprj ind expr ->
    --   let len :: TupleIdx tr a -> Int
    --       len ZeroTupIdx     = 0
    --       len (SuccTupIdx x) = 1 + len x
    --   in T.TupleRefFromRight (getAccTypePre eacc) (len ind) <$> convertAcc expr
    Aprj idx ex -> doAprj idx ex 
      where

        doAprj :: forall aenv arrs a . (Sug.Arrays a, Sug.Arrays arrs)
                  => TupleIdx (TupleRepr arrs) a
                  -> OpenAcc aenv arrs
                  -> EnvM TAExp 
        doAprj idx ex = do 
          let n = convertATupleIdx idx arrR
              len = aTupleNumLeaves arrRTop
          ex' <- convertAcc ex
          return $ T.TupleRefFromRight (getAccType ex) n len ex' 
          where
            arrR = Sug.arrays (undefined :: arrs) :: Sug.ArraysR (Sug.ArrRepr arrs)
            arrRTop = Sug.arrays (undefined :: a) :: Sug.ArraysR (Sug.ArrRepr a)
          
          -- = Sug.arrays (undefined :: a
      -- let n = convertATupleIdx (idx 
      --                  ty = getAccTypePre eacc
      --                  nom = convertToTupleType $ getAccTypePre ex -- Sug.expType ex
      --                  len = tupleNumLeaves ty
      --              in T.TupleRefFromRight (getAccTypePre eacc) n len <$> T.convertAExps ex  
-- Prj idx ex -> let n   = convertTupleIdx idx nom
--                       ty  = getExpType e
--                       nom = Sug.expType ex
--                       len = tupleNumLeaves ty
--                   in
--                    -- maybtrace ("TUPLE NUM LEAVES: e:"++show ty++ " " ++ show len ++ " " ++ show n) $
--                    T.ETupProject n len <$> convertExp ex

 
 
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
                  (convertSliceIndex sliceIndex)
                  <$> convertExp slix
                  <*> convertAcc a
    Slice sliceIndex acc slix ->
      T.Index (getAccTypePre eacc) (convertSliceIndex sliceIndex) <$> convertAcc acc
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


    Transform _sh _p _f _a      -> error "ToAccClone.convertAcc: Transform not supported"
    Awhile _p _f _x             -> error "ToAccClone.convertAcc: Awhile not supported"
    Aforeign _ff _afun _a       -> error "ToAccClone.convertAcc: Aforeign not supported"


--------------------------------------------------------------------------------
-- Convert Accelerate Scalar Expressions
--------------------------------------------------------------------------------

-- | Simply throws away type-level information associated with a
-- `SliceIndex`.  Returns a normal cons-list (instead of the Snoc-list).
convertSliceIndex :: SliceIndex slix sl co dim -> S.SliceType
convertSliceIndex (SliceNil)            = []
convertSliceIndex (SliceAll   sliceIdx) = S.All   : convertSliceIndex sliceIdx
convertSliceIndex (SliceFixed sliceIdx) = S.Fixed : convertSliceIndex sliceIdx

-- convert Array Tuple indices
convertATupleIdx :: TupleIdx t e -> Sug.ArraysR a -> Int
convertATupleIdx ZeroTupIdx  _  = 0
convertATupleIdx (SuccTupIdx i) (Sug.ArraysRpair r2 r1)  = sizeATup r1 + convertATupleIdx i r2

sizeATup :: Sug.ArraysR a -> Int 
sizeATup Sug.ArraysRunit         = 0
sizeATup (Sug.ArraysRpair r1 r2) = sizeATup r1  + sizeATup r2 
sizeATup Sug.ArraysRarray        = 1

-- Compute Number of leaves in a Array Tuple
aTupleNumLeaves :: Sug.ArraysR a -> Int
aTupleNumLeaves = sizeATup 

-- For now I'm leaving it as an index from the right with no length:
-- BJS + T: Fixing this to take tuple structure into consideration. 
convertTupleIdx :: TupleIdx t e ->  TupleType a -> Int
convertTupleIdx = prjToInt 

prjToInt :: TupleIdx t e -> TupleType a -> Int
prjToInt ZeroTupIdx     _                 = 0
prjToInt (SuccTupIdx i) (b `PairTuple` a) = sizeTupleType a + prjToInt i b
prjToInt _              _                 = error "prjToInt: inconsistent valuation"

sizeTupleType :: TupleType a -> Int
sizeTupleType UnitTuple       = 0
sizeTupleType (SingleTuple _) = 1
sizeTupleType (PairTuple a b) = sizeTupleType a + sizeTupleType b


-- loop tix
--  where
--   loop :: TupleIdx t e -> Int
--   loop ZeroTupIdx       = 0
--   loop (SuccTupIdx idx) = 1 + loop idx

convertBoundary :: Boundary a -> S.Boundary
convertBoundary = error "convertBoundary: implement me" -- FIXME TODO

-- | Takes a closed expression
convertExp :: forall env aenv ans . OpenExp env aenv ans -> EnvM T.Exp
convertExp e =
  -- (\x -> do x' <- x
  --           trace ("CONVERTING EXP "++show e ++ " -> "++show x')
  --             (return x')) $
  case e of
    Let exp1 exp2 ->
      do e1     <- convertExp exp1
         (v,e2) <- withExtendedScalarEnv "e"$
                   convertExp exp2
         let sty = getExpType exp1
         return$ T.ELet (v,sty,e1) e2

    -- Here is where we get to peek at the type of a variable:
    Var idx ->
      do var <- envLookupScalar (idxToInt idx)
         return$ T.EVr var

    -- Lift let's outside of primapps so we can get to the tuple:
    -- This will be tricky because of changing the debruijn indicies:
    -- PrimApp p (Let e1 e2) -> convertExp (Let e1 (PrimApp p e2))
    PrimApp p arg -> convertPrimApp p arg

    Tuple tup -> convertTuple tup

    Const c   -> return$ T.EConst$
                 convertConst (Sug.eltType (typeOnlyErr "convertExp" ::ans)) c

    -- NOTE: The incoming AST indexes tuples FROM THE RIGHT:
    Prj idx ex -> let n   = convertTupleIdx idx nom
                      ty  = getExpType e
                      nom = Sug.expType ex
                      len = tupleNumLeaves ty
                  in
                   -- maybtrace ("TUPLE NUM LEAVES: e:"++show ty++ " " ++ show len ++ " " ++ show n) $
                   T.ETupProject ty n len <$> convertExp ex

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
    IndexAny       -> error "ToAccClone.hs: not expecting to observe IndexAny value."
      -- return T.EIndexAny

    -- New, unhandled cases:
    -- ---------------------

    -- TLM: the conversion of IndexSlice and IndexFull needs to be done later in
    --      the pipeline, after at least UnzipETups.
    --
    IndexSlice _sliceIndex _slix _sh -> do
      error "ToAccClone: TODO: handle IndexSlice"

    IndexFull _sliceIndex _slix _sl -> do
      error "ToAccClone: TODO: handle IndexFull"

    ToIndex{}     -> error "ToAccClone.hs: TODO: handle ToIndex"
    FromIndex{}   -> error "ToAccClone.hs: TODO: handle FromIndex"
    LinearIndex{} -> error "ToAccClone.hs: TODO: handle LinearIndex"
    Intersect{}   -> error "ToAccClone.hs: TODO: handle Intersect"
    Foreign{}     -> error "ToAccClone.hs: TODO: handle ForeignExp"

    Cond c t ex -> T.ECond <$> convertExp c
                           <*> convertExp t
                           <*> convertExp ex

    While f1 f2 ex -> T.EWhile <$> convertFun1 f1
                               <*> convertFun1 f2
                               <*> convertExp ex

    Index acc eix -> T.EIndexScalar <$> convertAcc acc
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
convertTuple :: Tuple (PreOpenExp OpenAcc env aenv) t' -> EnvM T.Exp
convertTuple NilTup = return$ T.ETuple []
convertTuple (SnocTup tup e) =
    -- trace ("CONVERTING TUPLE "++show (e))$
    do e'   <- convertExp e
       tup' <- convertTuple tup
       case tup' of
         T.ETuple ls -> return$ T.ETuple$ ls ++ [e'] -- Snoc!
         se -> error$ "convertTuple: expected a tuple expression, received:\n  "++ show se


tupleNumLeaves :: S.Type -> Int
tupleNumLeaves (S.TTuple ls) = L.sum $ L.map tupleNumLeaves ls
tupleNumLeaves _             = 1


--------------------------------------------------------------------------------
-- Convert types
-------------------------------------------------------------------------------

-- | Generate the simple type representation of a _surface_ type
--
convertEltType :: forall a. Sug.Elt a => a -> S.Type
convertEltType _ = reconstruct structure -- simpleType
  where
    structure           = Sug.eltRep (undefined :: a)
    simpleType          = cvt (Sug.eltType (undefined :: a))

--    reconstruct :: (Sug.EltR a) -> [S.Type] -> S.Type
    reconstruct :: forall a' . (Sug.EltR a') -> S.Type    
    reconstruct rep =
      case rep of
        Sug.EltR_Z   -> error "convertEltType: finish Z"
        Sug.EltR_All -> error "convertEltType: finish All"
        Sug.EltR_Any sh -> error "convertEltType: finish Any"        
        Sug.EltR_Int8  -> S.TInt8
        Sug.EltR_Int16 -> S.TInt16
        Sug.EltR_Int32 -> S.TInt32
        Sug.EltR_Int64 -> S.TInt64
        Sug.EltR_Word  -> S.TWord
        Sug.EltR_Word8 -> S.TWord8
        Sug.EltR_Word16 -> S.TWord16
        Sug.EltR_Word32 -> S.TWord32
        Sug.EltR_Word64 -> S.TWord64
        Sug.EltR_CShort  -> S.TCShort
        Sug.EltR_CUShort -> S.TCUShort
        Sug.EltR_CInt    -> S.TCInt
        Sug.EltR_CUInt   -> S.TCUInt
        Sug.EltR_CLong   -> S.TCLong
        Sug.EltR_CULong  -> S.TCULong
        Sug.EltR_CLLong  -> S.TCLLong
        Sug.EltR_CULLong -> S.TCULLong
        Sug.EltR_Float   -> S.TFloat
        Sug.EltR_Double  -> S.TDouble
        Sug.EltR_CFloat  -> S.TCFloat
        Sug.EltR_CDouble -> S.TCDouble
        Sug.EltR_Bool    -> S.TBool
        Sug.EltR_Char    -> S.TChar
        Sug.EltR_CChar   -> S.TCChar
        Sug.EltR_CSChar  -> S.TCSChar
        Sug.EltR_CUChar  -> S.TCUChar

        -- Need type level evidence that a ~ (b,c), to do this:
        Sug.EltR_Tup2 a b ->
          error "finishme "
          -- S.TTuple [reconstruct a, reconstruct b]

{-
        x | Just (Sug.EltR_Tup2 a b) <- cast x
        
        _ -> case prod (undefined :: a) of
               ProdRunit -> S.TUnit
               ProdRsnoc ProdRunit -> undefined -- (,)
               ProdRsnoc (ProdRsnoc ProdRunit) ->
                 --- ((((),a),b),c) ~~> (a,b,c)  EltR_Tup3
                 undefined -- (,,)
-}
        
        other -> error "FINISHME"
{-    
    reconstruct (Sug.ZKind,   _)    tys = mkTuple tys           -- shapes/indices
    reconstruct (Sug.TupKind, tree) tys = snd $ go tree tys     -- regular element types
      where
        go :: Sug.TupTree -> [S.Type] -> ([S.Type], S.Type)
        go Sug.TupLeaf     []     = error "convertEltType: inconsistent valuation"
        go Sug.TupLeaf     (x:xs) = (xs, x)
        go (Sug.TupTree t) xs     = let (xs', t') = L.mapAccumL (flip go) xs t
                                    in  (xs', mkTuple t')
-}

    -- This produces a flat list of scalar types only:
    cvt :: TupleType t -> [S.Type]
    cvt UnitTuple         = []
    cvt (PairTuple t1 t0) = cvt t1 ++ cvt t0
    cvt (SingleTuple ty)  = return $
      case ty of
        NumScalarType (IntegralNumType ty') ->
          case ty' of
            TypeInt{}     -> S.TInt
            TypeInt8{}    -> S.TInt8
            TypeInt16{}   -> S.TInt16
            TypeInt32{}   -> S.TInt32
            TypeInt64{}   -> S.TInt64
            TypeWord{}    -> S.TWord
            TypeWord8{}   -> S.TWord8
            TypeWord16{}  -> S.TWord16
            TypeWord32{}  -> S.TWord32
            TypeWord64{}  -> S.TWord64
            TypeCShort{}  -> S.TCShort
            TypeCInt{}    -> S.TCInt
            TypeCLong{}   -> S.TCLong
            TypeCLLong{}  -> S.TCLLong
            TypeCUShort{} -> S.TCUShort
            TypeCUInt{}   -> S.TCUInt
            TypeCULong{}  -> S.TCULong
            TypeCULLong{} -> S.TCULLong
        NumScalarType (FloatingNumType ty') ->
          case ty' of
            TypeFloat{}   -> S.TFloat
            TypeDouble{}  -> S.TDouble
            TypeCFloat{}  -> S.TCFloat
            TypeCDouble{} -> S.TCDouble
        NonNumScalarType ty' ->
          case ty' of
            TypeBool{}    -> S.TBool
            TypeChar{}    -> S.TChar
            TypeCChar{}   -> S.TCChar
            TypeCSChar{}  -> S.TCSChar
            TypeCUChar{}  -> S.TCUChar


-- | Generate the simple type representation of a _surface_ type
--
convertArrayType :: forall arrs. Sug.Arrays arrs => arrs -> S.Type
convertArrayType _ = reconstruct structure simpleType
  where
    structure = error "convertArrayType: need array analogue for eltRep"
--      Sug.reifyArrTupTree (undefined :: arrs)
    simpleType  = cvt (Sug.arrays (undefined :: arrs))

--    reconstruct :: Sug.TupTree -> [S.Type] -> S.Type
    reconstruct = error "convertArrayType/reconstruct - finishme"
{-    
    reconstruct tree tys = snd $ go tree tys
      where
        go :: Sug.TupTree -> [S.Type] -> ([S.Type], S.Type)
        go Sug.TupLeaf     []     = error "convertType: inconsistent valuation"
        go Sug.TupLeaf     (x:xs) = (xs, x)
        go (Sug.TupTree t) xs     = let (xs', t') = L.mapAccumL (flip go) xs t
                                    in  (xs', mkTuple t')
-}
    cvt :: Sug.ArraysR a -> [S.Type]
    cvt Sug.ArraysRunit         = []
    cvt (Sug.ArraysRpair a1 a0) = cvt a1 ++ cvt a0
    cvt arr@Sug.ArraysRarray
      | _ :: Sug.ArraysR (Sug.Array sh e) <- arr
      = [S.TArray (Sug.dim (undefined::sh)) (convertEltType (undefined :: e))]


-- | Constructor that refuses to make singleton tuple types.
--
mkTuple :: [S.Type] -> S.Type
mkTuple [ty] = ty
mkTuple ls = S.TTuple ls


--------------------------------------------------------------------------------
-- Convert constants
-------------------------------------------------------------------------------

-- convertConst :: Sug.Elt t => Sug.EltRepr t -> S.Const
convertConst :: TupleType a -> a -> S.Const
convertConst ty0 c0 =
  -- (\x -> x `seq` maybtrace ("[ToAccClone] Converting tuple const: "++show ty0++" -> "++show x) x) $
  branch ty0 c0
 where
 -- Follow the leftmost side
 spine :: TupleType a -> a -> [S.Const]
 spine ty c =
  -- (\x -> x `seq` maybtrace (" *: Spine "++show ty++" -> "++show x) x) $
  case ty of
    UnitTuple -> []
    PairTuple ty1 ty0 -> let (c1,c0) = c
                             c0' = branch ty0 c0
                         in c0' : spine ty1 c1
--                         in spine ty1 c1 ++ [c0'] -- Snoc.
    SingleTuple scalar -> error $ "convertConst: bad tuple, should not see a scalar on the leftmost path."

 branch :: TupleType a -> a -> S.Const
 branch ty c =
  -- (\x -> x `seq` maybtrace (" *: Branch "++show ty++" -> "++show x) x) $
  case ty of
    UnitTuple -> S.Tup []
    -- This begins a new tuple:
    PairTuple ty1 ty0 -> let (c1,c0) = c
                             c0' = branch ty0 c0
                         in
                         case spine ty1 c1 of
                           [] -> c0'
                           ls -> S.Tup (c0' : ls)
--                           ls -> S.Tup (ls ++ [c0']) -- Snoc
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
   op :: PrimFun (a -> b) -> S.Prim
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
                                   sty = convertEltType (undefined :: arg)
                               (_,x) <- withExtendedScalarEnv "v" $ do
                                          v <- envLookupScalar 0
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

-- | This converts Accelerate Arrays data to the simplified representation.
--
--   Note that this does NOT need to do a deep copy, because the data payload
--   representation stays the same.
--
unpackArray :: forall arrs. Sug.Arrays arrs => arrs -> [S.AccArray]
unpackArray arrs = cvt (Sug.arrays (undefined::arrs)) (Sug.fromArr arrs)
  where
    cvt :: Sug.ArraysR a -> a -> [S.AccArray]
    cvt Sug.ArraysRunit           ()       = []
    cvt (Sug.ArraysRpair ar1 ar0) (a1, a0) = cvt ar1 a1 ++ cvt ar0 a0
    cvt Sug.ArraysRarray          a        = [cvtA a]

    cvtA :: forall sh e. (Sug.Shape sh, Sug.Elt e) => Sug.Array sh e -> S.AccArray
    cvtA (Sug.Array sh adata) = S.AccArray aty dims payload
      where
        dims    = shapeToList sh
        aty     = convertArrayType (undefined :: Sug.Array sh e)
        payload = unpack arrayElt adata

        unpack :: ArrayEltR a -> ArrayData a -> [S.ArrayPayload]
        unpack ArrayEltRint    (AD_Int   x)  = [S.ArrayPayloadInt x]
        unpack ArrayEltRint8   (AD_Int8  x)  = [S.ArrayPayloadInt8 x]
        unpack ArrayEltRint16  (AD_Int16 x)  = [S.ArrayPayloadInt16 x]
        unpack ArrayEltRint32  (AD_Int32 x)  = [S.ArrayPayloadInt32 x]
        unpack ArrayEltRint64  (AD_Int64 x)  = [S.ArrayPayloadInt64 x]
        unpack ArrayEltRword   (AD_Word   x) = [S.ArrayPayloadWord x]
        unpack ArrayEltRword8  (AD_Word8  x) = [S.ArrayPayloadWord8 x]
        unpack ArrayEltRword16 (AD_Word16 x) = [S.ArrayPayloadWord16 x]
        unpack ArrayEltRword32 (AD_Word32 x) = [S.ArrayPayloadWord32 x]
        unpack ArrayEltRword64 (AD_Word64 x) = [S.ArrayPayloadWord64 x]
        unpack ArrayEltRfloat  (AD_Float  x) = [S.ArrayPayloadFloat x]
        unpack ArrayEltRdouble (AD_Double x) = [S.ArrayPayloadDouble x]
        unpack ArrayEltRbool   (AD_Bool   x) = [S.ArrayPayloadBool x]
        unpack ArrayEltRchar   (AD_Char   x) = [S.ArrayPayloadChar x]
        unpack ArrayEltRunit   _             = []
        unpack (ArrayEltRpair aeR1 aeR0) ad  = unpack aeR1 (fstArrayData ad) ++ unpack aeR0 (sndArrayData ad)


-- | Almost an inverse of `unpackArray` -- repack the simplified data
--   representation with the type information necessary to form a proper
--   Accelerate array.
--
packArray :: forall sh elt . (Sug.Elt elt, Sug.Shape sh) => S.AccArray -> Sug.Array sh elt
packArray orig@(S.AccArray _ty dims origPayloads) =
  -- TEMP: FIXME:  [2012.11.21]  Temporarily allowing mismathched dimensions as long as the # elements is right:
--  if length dims == length dims' then -- Is the expected rank correct?
--  if product dims == product dims'

--  maybtrace ("[packArray]: BKit dims "++show dims++" Acc dims' "++show dims') $
  if (length dims == length dims') || (length dims' <= 1) -- Allowing mismatch for 0/1 dim.
  then Sug.Array shpVal (packit (typeOnlyErr "packArray1"::Sug.Array sh elt) (reverse origPayloads))
  else error$"SimpleConverter.packArray: array does not have the expected shape: "++show dims++" expected "++show dims'
 where

  -- We must us the *real* dims here to get the exact shape, and not just the rank:
  shpVal :: Sug.EltRepr sh = Sug.fromElt (Sug.listToShape (if dims' == [] then [] else dims) :: sh)
  dims' :: [Int] = Sug.shapeToList (Sug.ignore::sh)

  packit :: forall sh elt . (Sug.Shape sh, Sug.Elt elt) => Sug.Array sh elt -> [S.ArrayPayload] -> (ArrayData (Sug.EltRepr elt))
  packit _ pays = fst $ loop eTy pays
     where eTy = Sug.eltType (typeOnlyErr"packArray2"::elt)

  -- This consumes from a list of payloads and returns what is left in addition to the return value.
  loop :: forall elt . TupleType elt -> [S.ArrayPayload] -> (ArrayData elt, [S.ArrayPayload])
  loop tupTy payloads =
   -- maybtrace ("packArray: LOOPING "++show (length payloads)++" payload(s), tupty: "++
   --           show tupTy ++"\n   "++show (payloads)) $
   let err2 :: forall a . String -> a
       err2 msg = error$"packArray: given a AccArray of the wrong type, expected "++msg
                  ++" received "++ show(length payloads) ++ " payloads: "++paystr
       paystr = "\n"++(unlines$ L.map (take 200 . show) payloads) ++ "\n dimension: "++show dims
   in
   case (tupTy, payloads) of
    (UnitTuple,ls)     -> (AD_Unit,ls)

    -- Tuples are trees of SNOC operations in Accelerate currently:
    -- In SimpleAST we ignore the extra unit on the end in the AccArray representation:
--    (PairTuple UnitTuple (r::TupleType b),_)  -> AD_Pair AD_Unit (loop r payloads)
    -- This might occur given our representation of `All` in slice descriptors:
    -- But these units DON'T have a physical representation in the payloads:
--    (PairTuple (r::TupleType b) UnitTuple, _) -> AD_Pair (loop r payloads) AD_Unit
    (PairTuple t1 t2, ls)  ->
       let (res2,rst)  = loop t2 ls
           (res1,rst') = loop t1 rst
       in (AD_Pair res1 res2, rst')

    (SingleTuple (NumScalarType (FloatingNumType (TypeFloat  _))), S.ArrayPayloadFloat  uarr :rst) -> (AD_Float uarr, rst)
    (SingleTuple (NumScalarType (FloatingNumType (TypeDouble _))), S.ArrayPayloadDouble uarr :rst) -> (AD_Double uarr, rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt    _))), S.ArrayPayloadInt    uarr :rst) -> (AD_Int    uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt8   _))), S.ArrayPayloadInt8   uarr :rst) -> (AD_Int8   uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt16  _))), S.ArrayPayloadInt16  uarr :rst) -> (AD_Int16  uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt32  _))), S.ArrayPayloadInt32  uarr :rst) -> (AD_Int32  uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt64  _))), S.ArrayPayloadInt64  uarr :rst) -> (AD_Int64  uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord   _))), S.ArrayPayloadWord   uarr :rst) -> (AD_Word   uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord8  _))), S.ArrayPayloadWord8  uarr :rst) -> (AD_Word8  uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord16 _))), S.ArrayPayloadWord16 uarr :rst) -> (AD_Word16 uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord32 _))), S.ArrayPayloadWord32 uarr :rst) -> (AD_Word32 uarr,rst)
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord64 _))), S.ArrayPayloadWord64 uarr :rst) -> (AD_Word64 uarr,rst)

    (SingleTuple (NonNumScalarType (TypeBool _)), S.ArrayPayloadBool uarr :rst) -> (AD_Bool uarr,rst)
    (SingleTuple (NonNumScalarType (TypeChar _)), S.ArrayPayloadChar uarr :rst) -> (AD_Char uarr,rst)

    (SingleTuple (NumScalarType (FloatingNumType (TypeCFloat   _))), _) -> error "not supported yet: array of CFloat"
    (SingleTuple (NumScalarType (FloatingNumType (TypeCDouble  _))), _) -> error "not supported yet: array of CDouble"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCShort   _))), _) -> error "not supported yet: array of CShort"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCUShort  _))), _) -> error "not supported yet: array of CUShort"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCInt     _))), _) -> error "not supported yet: array of CInt"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCUInt    _))), _) -> error "not supported yet: array of CUInt"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCLong    _))), _) -> error "not supported yet: array of CLong"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCULong   _))), _) -> error "not supported yet: array of CULong"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCLLong   _))), _) -> error "not supported yet: array of CLLong"
    (SingleTuple (NumScalarType (IntegralNumType (TypeCULLong  _))), _) -> error "not supported yet: array of CULLong"
    (SingleTuple (NonNumScalarType (TypeCChar _)), _)  -> error "not supported yet: array of CChar"
    (SingleTuple (NonNumScalarType (TypeCSChar _)), _) -> error "not supported yet: array of CSChar"
    (SingleTuple (NonNumScalarType (TypeCUChar _)), _) -> error "not supported yet: array of CUChar"

    -- We could have a single catch-all cases here, but blowing it up
    -- like this allows meaningful feedback from -fwarn-incomplete-patterns:
    (SingleTuple (NumScalarType (FloatingNumType (TypeFloat  _))), _) -> err2 "Float"
    (SingleTuple (NumScalarType (FloatingNumType (TypeDouble _))), _) -> err2 "Double"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt    _))), _) -> err2 "Int"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt8   _))), _) -> err2 "Int8"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt16  _))), _) -> err2 "Int16"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt32  _))), _) -> err2 "Int32"
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt64  _))), _) -> err2 "Int64"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord   _))), _) -> err2 "Word"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord8  _))), _) -> err2 "Word8"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord16 _))), _) -> err2 "Word16"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord32 _))), _) -> err2 "Word32"
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord64 _))), _) -> err2 "Word64"
    (SingleTuple (NonNumScalarType (TypeBool _)), _) -> err2 "Bool"
    (SingleTuple (NonNumScalarType (TypeChar _)), _) -> err2  "Char"


-- | Repackage a result in simplified form as an properly-typed result
--   of an Acc computation, i.e. a real Accelerate array.
repackAcc :: forall a . Sug.Arrays a => Sug.Acc a -> [S.AccArray] -> a
repackAcc dummy simpls =
      maybtrace (" [repackAcc] ... "++show rep++", given "++show (length simpls)++" arrs\n") $
--              ++ unlines(L.map (("   "++) . show) simpls)) $  -- This bit prints the whole array
      Sug.toArr converted
  where
   converted :: Sug.ArrRepr a = fst$ cvt rep (reverse simpls)
   -- Pull some information out of thin air (from type domain to value domain):
   rep :: Sug.ArraysR (Sug.ArrRepr a) =
     Sug.arrays (error"SimpleInterp.run: this should never be used" :: a)

   -- In additon to a result, returns unused input arrays:
   cvt :: forall a' . Sug.ArraysR a' -> [S.AccArray] -> (a',[S.AccArray])
   cvt arrR simpls =
     -- maybtrace ("  repackAcc/cvt: simplls "++show simpls) $
     case arrR of
       -- This means ZERO arrays in the tuple-of-arrays:
       Sug.ArraysRunit ->
         trace (" In ArraysRunit case..." ) $
         ((),simpls)

       -- We don't explicitly represent this extra capstone-unit in the AccArray:
       Sug.ArraysRpair Sug.ArraysRunit r ->
         -- maybtrace (" [repackAcc] In ArraysRpair/UNIT case..." ) $
           let (res,rst) = cvt r simpls in
           (((), res), rst)
       Sug.ArraysRpair r1 r2 ->
         -- maybtrace (" [repackAcc] In ArraysRpair case..." ) $
           -- Dole out the available input arrays to cover the
           -- leaves, filling in the right first:
           let (res2,rst)  = cvt r2 simpls
               (res1,rst') = cvt r1 rst
           in ((res1,res2), rst')

       Sug.ArraysRarray | (rep :: Sug.ArraysR (Sug.Array sh elt)) <- arrR ->
         -- maybtrace (" [repackAcc] In ArraysRarray case..." ) $
         case simpls of
           []   -> error$"repackAcc2: ran out of input arrays.\n"
           l:ls -> (packArray l :: Sug.Array sh elt, ls)

{-- TLM: I believe this is no longer necessary, as it looks that
 --      SimpleArray.reglueArrayofTups is already tupling the arrays.
 --
               -- Once we have peeled off "one" array, we still need to unzip
               -- the tupled elements.
               let elTy   = Sug.eltType (undefined::elt)
                   elWid  = eltWidth elTy
                   zipped = SA.concatAccArrays$ take elWid ls
               in
                 -- maybtrace (" ... about to zip "++show (elTy, elWid, rep)) $
                 ((packArray zipped) :: (Sug.Array sh elt),
                   drop elWid ls)
--}

   -- How many scalar components are there in an element type?
   eltWidth :: forall a . TupleType a -> Int
   eltWidth UnitTuple       = 1
   eltWidth (SingleTuple _) = 1
   eltWidth x@(PairTuple _ _) = tupLoop x


   -- Once we start at tuple, we expect the eltType representation MUST bottom out to ((),_).
   tupLoop :: forall a . TupleType a -> Int
   tupLoop (PairTuple UnitTuple b) = eltWidth b
   tupLoop (PairTuple a b) = tupLoop a + eltWidth b
   tupLoop (SingleTuple x) = error$"repackAcc/tupLoop: once we start a tuple it must terminate in Unit, not SingleTuple "++show x
   tupLoop UnitTuple       = error "repackAcc/tupLoop: once we start a tuple it must terminate in (PairTuple Unit _), not a naked UnitTuple."

instance Show (Sug.ArraysR a') where
  show arrR = "ArraysR "++loop arrR
   where
    loop :: forall ar .  Sug.ArraysR ar -> String
    loop arrR =
     case arrR of
       Sug.ArraysRunit       -> "()"
       Sug.ArraysRpair r1 r2 -> "("++ loop r1 ++", "++ loop r2++")"
       Sug.ArraysRarray      -> "Array"

mkArrayTuple :: a -> [T.AExp a] -> T.AExp a
mkArrayTuple ty [one] = one
mkArrayTuple ty ls    = T.ArrayTuple ty ls

