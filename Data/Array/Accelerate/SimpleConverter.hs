{-# LANGUAGE BangPatterns, GADTs, ScopedTypeVariables, CPP, TupleSections  #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- {-# ANN module "HLint: ignore Eta reduce" #-}

-- TODO LIST:
--   * Implement Use
--   * Audit treatment of shapes and indices
--   * Audit tuple flattening guarantees
--   * Add type info to some language forms... 


module Data.Array.Accelerate.SimpleConverter 
       ( 
         convertToSimpleAST, 
         unpackArray, packArray, repackAcc,
         
         -- TEMP:
         tt         
       )
       where

-- standard libraries
import Control.Monad
import Control.Applicative ((<$>),(<*>))
import Prelude                                     hiding (sum)
import Control.Monad.State.Strict (State, evalState, get, put)

-- friends
import Data.Array.Accelerate.Type                  
import Data.Array.Accelerate.Array.Data            
import Data.Array.Accelerate.Array.Representation  hiding (sliceIndex)
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Tuple
-- import Data.Array.Accelerate.Analysis.Shape (accDim)
import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.SimpleAST as S

import qualified Data.List as L

import Debug.Trace(trace)
-- tracePrint s x = trace (s ++ show x) x

--------------------------------------------------------------------------------
-- Exposed entrypoints for this module:
--------------------------------------------------------------------------------

-- | Convert the sophisticate Accelerate-internal AST representation
--   into something very simple for external consumption.
convertToSimpleAST :: Sug.Arrays a => Sug.Acc a -> S.AExp
convertToSimpleAST = runEnvM . convertAcc . Sug.convertAcc

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
  where  ty  = Sug.eltType ((error"This shouldn't happen (0)")::ans) 


typeOnlyErr msg = error$ msg++ ": This is a value that should never be evaluated.  It carries type information only."

--------------------------------------------------------------------------------
-- Convert Accelerate Array-level Expressions
--------------------------------------------------------------------------------

        
-- convertAcc :: Delayable a => OpenAcc aenv a -> EnvM S.AExp
convertAcc :: OpenAcc aenv a -> EnvM S.AExp
convertAcc (OpenAcc cacc) = convertPreOpenAcc cacc 
 where 
 cvtSlice :: SliceIndex slix sl co dim -> S.SliceType
 cvtSlice (SliceNil)            = []
 cvtSlice (SliceAll   sliceIdx) = S.All   : cvtSlice sliceIdx 
 cvtSlice (SliceFixed sliceIdx) = S.Fixed : cvtSlice sliceIdx 

 convertPreOpenAcc :: forall aenv a . 
                      PreOpenAcc OpenAcc aenv a -> EnvM S.AExp
 convertPreOpenAcc eacc = 
  case eacc of 
    Alet acc1 acc2 -> 
       do a1     <- convertAcc acc1
          (v,a2) <- withExtendedEnv "a"$ 
                    convertAcc acc2 
          let sty = getAccType acc1
          return$ S.Let v sty a1 a2

    Avar idx -> 
      do var <- envLookup (idxToInt idx)
         return$ S.Vr var

    ------------------------------------------------------------
    -- Array creation:
    -- These should include types.
    
    Generate sh f -> S.Generate (getAccTypePre eacc)
                                <$> convertExp sh
                                <*> convertFun f

    -- This is real live runtime array data:
    Use (arrrepr :: Sug.ArrRepr a) ->
         -- This is rather odd, but we need to have a dummy return
         -- value to avoid errors about ArrRepr type functions not
         -- being injective.
         let (ty,arr,_::Phantom a) = unpackArray arrrepr in 
         return$ S.Use ty arr 

    -- End Array creation prims.
    ------------------------------------------------------------

    Acond cond acc1 acc2 -> S.Cond <$> convertExp cond 
                                   <*> convertAcc acc1 
                                   <*> convertAcc acc2

    Apply (Alam (Abody funAcc)) acc -> 
      do (v,bod) <- withExtendedEnv "a" $ convertAcc funAcc
         let sty = getAccType acc
         S.Apply (S.ALam [(v, sty)] bod) <$> convertAcc acc

    Apply _afun _acc -> error "This case is impossible"

    Atuple (atup :: Atuple (OpenAcc aenv) b ) -> 
      let loop :: Atuple (OpenAcc aenv') a' -> EnvM [S.AExp] 
          loop NilAtup = return [] 
          loop (SnocAtup t a) = do first <- convertAcc a
                                   rest  <- loop t
                                   return (first : rest)
      in do ls <- loop atup
            return$ S.ArrayTuple (reverse ls)

    Aprj ind expr -> 
      let len :: TupleIdx tr a -> Int 
          len ZeroTupIdx     = 0
          len (SuccTupIdx x) = 1 + len x
      in S.TupleRefFromRight (len ind) <$> convertAcc expr

    Unit e        -> S.Unit <$> convertExp e 

    Map     f acc       -> S.Map     <$> convertFun f 
                                     <*> convertAcc acc
    ZipWith f acc1 acc2 -> S.ZipWith <$> convertFun f
                                     <*> convertAcc acc1
                                     <*> convertAcc acc2
    Fold     f e acc -> S.Fold  <$> convertFun f
                                <*> convertExp e 
                                <*> convertAcc acc
    Fold1    f   acc -> S.Fold1 <$> convertFun f
                                <*> convertAcc acc
    FoldSeg  f e acc1 acc2 -> S.FoldSeg  <$> convertFun f
                                         <*> convertExp e
                                         <*> convertAcc acc1
                                         <*> convertAcc acc2
    Fold1Seg f   acc1 acc2 -> S.Fold1Seg <$> convertFun f
                                         <*> convertAcc acc1
                                         <*> convertAcc acc2
    Scanl  f e acc -> S.Scanl  <$> convertFun f
                               <*> convertExp e 
                               <*> convertAcc acc
    Scanl' f e acc -> S.Scanl' <$> convertFun f
                               <*> convertExp e 
                               <*> convertAcc acc
    Scanl1 f   acc -> S.Scanl1 <$> convertFun f
                               <*> convertAcc acc
    Scanr  f e acc -> S.Scanr  <$> convertFun f
                               <*> convertExp e 
                               <*> convertAcc acc
    Scanr' f e acc -> S.Scanr' <$> convertFun f
                               <*> convertExp e 
                               <*> convertAcc acc
    Scanr1 f   acc -> S.Scanr1 <$> convertFun f
                               <*> convertAcc acc

    Replicate sliceIndex slix a ->       
      S.Replicate (cvtSlice sliceIndex) <$> convertExp slix 
                                        <*> convertAcc a
    Index sliceIndex acc slix -> 
      S.Index (cvtSlice sliceIndex)     <$> convertAcc acc
                                        <*> convertExp slix
    Reshape e acc -> S.Reshape <$> convertExp e <*> convertAcc acc
    Permute fn dft pfn acc -> S.Permute <$> convertFun fn 
                                        <*> convertAcc dft
                                        <*> convertFun pfn
                                        <*> convertAcc acc
    Backpermute e pfn acc -> S.Backpermute <$> convertExp e 
                                           <*> convertFun pfn
                                           <*> convertAcc acc 
    Stencil  sten bndy acc -> S.Stencil <$> convertFun sten
                                        <*> return (convertBoundary bndy)
                                        <*> convertAcc acc
    Stencil2 sten bndy1 acc1 bndy2 acc2 -> 
      S.Stencil2 <$> convertFun sten 
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
convertBoundary = error "convertBoundary: implement me"

-- Evaluate a closed expression
convertExp :: forall env aenv ans . OpenExp env aenv ans -> EnvM S.Exp
convertExp e = 
  case e of 
    Let exp1 exp2 -> 
      do e1     <- convertExp exp1
         (v,e2) <- withExtendedEnv "e"$ 
                   convertExp exp2 
         let sty = getExpType exp1
         return$ S.ELet v sty e1 e2
    
    -- Here is where we get to peek at the type of a variable:
    Var idx -> 
      do var <- envLookup (idxToInt idx)
         return$ S.EVr var
    
    -- Lift let's outside of primapps so we can get to the tuple:
    -- This will be tricky because of changing the debruijn indicies:
    -- PrimApp p (Let e1 e2) -> convertExp (Let e1 (PrimApp p e2))
    PrimApp p arg -> convertPrimApp p arg

    Tuple tup -> convertTuple tup

    Const c   -> return$ S.EConst$ 
                 convertConst (Sug.eltType (typeOnlyErr "convertExp" ::ans)) c

    -- NOTE: The incoming AST indexes tuples FROM THE RIGHT:
    Prj idx ex -> 
                 -- If I could get access to the IsTuple dict I could do something here:
                 -- The problem is the type function EltRepr....
                 let n = convertTupleIdx idx in 
--                 S.EPrj n m <$> convertExp e
                 S.ETupProjectFromRight n <$> convertExp ex

    -- This would seem to force indices to be LISTS at runtime??
    IndexNil       -> return$ S.EIndex []
    IndexCons esh ei -> do esh' <- convertExp esh
                           ei'  <- convertExp ei
                           return $ case esh' of
                             S.EIndex ls -> S.EIndex (ei' : ls)
                             _           -> S.EIndexConsDynamic ei' esh'
    IndexHead eix   -> do eix' <- convertExp eix
                          return $ case eix' of
                             -- WARNING: This is a potentially unsafe optimization:
                             -- Throwing away expressions:
                             S.EIndex (h:_) -> h 
                             S.EIndex []    -> error "IndexHead of empty index."
                             _              -> S.EIndexHeadDynamic eix'
    IndexTail eix   -> do eix' <- convertExp eix
                          return $ case eix' of
                             -- WARNING: This is a potentially unsafe optimization:
                             -- Throwing away expressions:
                             S.EIndex (_:tl) -> S.EIndex tl
                             S.EIndex []     -> error "IndexTail of empty index."
                             _               -> S.EIndexTailDynamic eix'
    IndexAny       -> return S.EIndexAny

    Cond c t ex -> S.ECond <$> convertExp c 
                           <*> convertExp t
                           <*> convertExp ex
    
    IndexScalar acc eix -> S.EIndexScalar <$> convertAcc acc
                                          <*> convertExp eix
    Shape acc -> S.EShape <$> convertAcc acc
    ShapeSize  acc -> S.EShapeSize  <$> convertExp acc

    -- We are committed to specific binary representations of numeric
    -- types anyway, so we simply encode special constants here,
    -- rather than preserving their specialness:
    PrimConst c -> return$ S.EConst $ 
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
convertTuple :: Tuple (PreOpenExp OpenAcc env aenv) t' -> EnvM S.Exp
convertTuple NilTup = return$ S.ETuple []
convertTuple (SnocTup tup e) = 
--    trace "convertTuple..."$
    do e' <- convertExp e
       tup' <- convertTuple tup
       case tup' of 
         S.ETuple ls -> return$ S.ETuple$ ls ++ [e']
         se -> error$ "convertTuple: expected a tuple expression, received:\n  "++ show se


--------------------------------------------------------------------------------
-- Convert types
-------------------------------------------------------------------------------

convertType :: TupleType a -> S.Type
convertType ty = 
  case ty of 
    UnitTuple -> S.TTuple []
    PairTuple ty1 ty0  -> 
      let ty0' = convertType ty0 in 
      -- Convert to Haskell-style tuples here (left-first, no unary tuples):
      case convertType ty1 of 
        S.TTuple [] -> ty0'
        S.TTuple ls -> S.TTuple (ty0' : ls)
        oth         -> S.TTuple [ty0', oth]
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
    case loop ty of 
      S.TTuple [S.TTuple [], realty] -> realty
      t -> error$ "SimpleConverter: made invalid assumuptions about array types from Acc frontend: "++show t
  where 
    loop :: forall arrs . Sug.ArraysR arrs -> S.Type
    loop ty = 
      case ty of 
       Sug.ArraysRunit  -> S.TTuple []
       -- Again, here we reify information from types (phantom type
       -- parameters) into a concrete data-representation:
       Sug.ArraysRarray | (_ :: Sug.ArraysR (Sug.Array sh e)) <- ty -> 
          let ety = Sug.eltType ((error"This shouldn't happen (3)")::e) in
--          S.TArray (Sug.dim (error"dimOnly"::sh)) (convertType ety)
          S.TArray (Sug.dim (Sug.ignore :: sh)) (convertType ety)          
                                                 
       Sug.ArraysRpair t0 t1 -> S.TTuple [loop t0, loop t1]

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

convertPrimApp :: (Sug.Elt a, Sug.Elt b)
               => PrimFun (a -> b) -> PreOpenExp OpenAcc env aenv a
               -> EnvM S.Exp
               
convertPrimApp p arg = 
  do 
     args2 <- convertExp arg
     return (loop args2)
 where 
   -- Push primapps inside lets:
   loop :: S.Exp -> S.Exp
   loop args' = case args' of 
                  S.ELet v sty e1 e2 ->
                    S.ELet v sty e1 (loop e2)
                  -- WARNING!  Need a sanity check on arity here:
                  S.ETuple ls -> mkPapp ls
                  oth         -> mkPapp [oth]
                  
   mkPapp ls = if length ls == arity
               then S.EPrimApp newprim ls
               else error$"SimpleConverter.convertPrimApp: wrong number of arguments to prim "
                    ++show newprim++": "++ show ls
   arity   = S.primArity newprim             
   newprim = op p 
   op pr   = 
    case pr of 
      PrimAdd _ty -> S.NP S.Add
      PrimMul _ty -> S.NP S.Mul
      PrimSig _ty -> S.NP S.Sig
      PrimAbs _ty -> S.NP S.Abs
      PrimNeg _ty -> S.NP S.Neg
      
      PrimQuot _ty -> S.IP S.Quot

      _ -> error$ "primapp not handled yet: "++show (PrimApp pr arg)

--------------------------------------------------------------------------------
-- Convert Accelerate Functions
--------------------------------------------------------------------------------

-- Convert an open, scalar function:
convertFun :: OpenFun e ae t0 -> EnvM S.Fun
convertFun =  loop [] 
 where 
   loop :: forall env aenv t . 
           [(S.Var,S.Type)] -> OpenFun env aenv t -> EnvM S.Fun
   loop acc (Body b) = do b'  <- convertExp b 
                          -- It would perhaps be nice to record the output type of function 
                          -- here as well.  But b's type isn't in class Elt.
                          return (S.Lam (reverse acc) b')
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
packArray orig@(S.AccArray dims payloads) = 
  if length dims == length dims'
  then Sug.Array shpVal (packit (typeOnlyErr "packArray1"::Sug.Array sh e) payloads)
  else error$"SimpleConverter.packArray: array does not have the expected dimensions: "++show dims++" expected "++show dims'
 where 
  shpVal :: Sug.EltRepr sh = Sug.fromElt (Sug.listToShape dims :: sh)
  dims' :: [Int] = Sug.shapeToList (Sug.ignore::sh)

  packit :: forall sh e . (Sug.Shape sh, Sug.Elt e) => Sug.Array sh e -> [S.ArrayPayload] -> (ArrayData (Sug.EltRepr e))
  packit _ [payload] = loop eTy payload
   where 
   eTy = Sug.eltType (typeOnlyErr"packArray2"::e) 

   loop :: forall e . TupleType e -> S.ArrayPayload -> (ArrayData e)
   loop tupTy payload =
    case (tupTy, payload) of
    (UnitTuple,_)     -> AD_Unit

    -- We ignore the extra unit on the end in the AccArray representation:
    (PairTuple UnitTuple (r::TupleType b),_) ->  AD_Pair AD_Unit (loop r payload) 

    (PairTuple _t1 _t2,_) -> let (_a1,_a2) = S.splitComponent orig in 
                           error$ "packArray: PairTuple should not be encountered here! Only one payload: "++ show payload
--                         AD_Pair (adata t1 (head payloads))
--                                 undefined

    (SingleTuple (NumScalarType (FloatingNumType (TypeFloat _))),  S.ArrayPayloadFloat uarr)  -> AD_Float uarr
    (SingleTuple (NumScalarType (FloatingNumType (TypeDouble _))), S.ArrayPayloadDouble uarr) -> AD_Double uarr

    (SingleTuple (NumScalarType (IntegralNumType (TypeInt   _))), S.ArrayPayloadInt   uarr) -> AD_Int uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt8  _))), S.ArrayPayloadInt8  uarr) -> AD_Int8 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt16 _))), S.ArrayPayloadInt16 uarr) -> AD_Int16 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt32 _))), S.ArrayPayloadInt32 uarr) -> AD_Int32 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt64 _))), S.ArrayPayloadInt64 uarr) -> AD_Int64 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord   _))), S.ArrayPayloadWord   uarr) -> AD_Word uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord8  _))), S.ArrayPayloadWord8  uarr) -> AD_Word8 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord16 _))), S.ArrayPayloadWord16 uarr) -> AD_Word16 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord32 _))), S.ArrayPayloadWord32 uarr) -> AD_Word32 uarr
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord64 _))), S.ArrayPayloadWord64 uarr) -> AD_Word64 uarr

    (SingleTuple (NonNumScalarType (TypeBool _)), S.ArrayPayloadBool uarr) -> AD_Bool uarr
    (SingleTuple (NonNumScalarType (TypeChar _)), S.ArrayPayloadChar uarr) -> AD_Char uarr

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
    (SingleTuple (NumScalarType (FloatingNumType (TypeFloat _))),  _) -> err2
    (SingleTuple (NumScalarType (FloatingNumType (TypeDouble _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt   _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt8  _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt16 _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt32 _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeInt64 _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord   _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord8  _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord16 _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord32 _))), _) -> err2
    (SingleTuple (NumScalarType (IntegralNumType (TypeWord64 _))), _) -> err2
    (SingleTuple (NonNumScalarType (TypeBool _)), _) -> err2
    (SingleTuple (NonNumScalarType (TypeChar _)), _) -> err2

  err2 = error "packArray: given a SimpleAST.AccArray of the wrong type."


-- | Repackage a result in simplified form as an properly typed result
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
       Sug.ArraysRpair r1 r2 -> let (a1,a2) = S.splitComponent simpl in 
                                (cvt r1 a1, cvt r2 a2)
       Sug.ArraysRarray | (_ :: Sug.ArraysR (Sug.Array sh e)) <- arrR ->
         (packArray simpl) :: (Sug.Array sh e)


tt = S.replicate [2] (S.F 3.3)

--------------------------------------------------------------------------------

