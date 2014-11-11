{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A library for the runtime construction of fully typed Accelerate programs.
--
-- In contrast with DynamicAcc.hs, this version uses the "Smart" (HOAS) AST
-- representation, rather than going straight to type-level De-bruijn indices.
--
-- TODO: If we want to use this seriously, then switch to template Haskell or
-- some other, better boilerplate elimination mechanism, not CPP macros.
--
-- TODO: We should simply TYPECHECK SimpleAcc expressions to get nice error
-- messages before putting them into the dynamic casting meat grinder below.

module Data.Array.Accelerate.DynamicAcc2 (

   -- * Functions to convert `SimpleAcc` programs into fully-typed Accelerate
   --   programs.
   convertProg, convertAcc, convertExp,

   -- * Dynamically typed AST pieces
   SealedExp, SealedAcc,
   downcastE, downcastA,

   -- * Computing types at runtime so as to downcast:
   scalarTypeD, SealedEltTuple(..),
   shapeTypeD,  SealedShapeType(..),
   arrayTypeD,  SealedArrayType(..),

   -- * Operating on open array and scalar expressions:
   convertOpenAcc, convertOpenExp,
   emptyEnvPack, extendA, extendE,

   -- * REEXPORTs: for convenience
   Type(..), Const(..), Phantom(..),

   -- * INTERNAL: Syntax-constructing functions, operating over
   -- `Sealed`, dynamic representations.
   constantE, dbgtrace,

) where

import Data.Array.Accelerate.BackendKit.CompilerPipeline        ( phase0, phase1 )
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone       ( repackAcc, expType )
import Data.Array.Accelerate.BackendKit.Utils.Helpers           ( Phantom(Phantom), maybtrace, dbg )
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc           ( Type(..), Const(..), AVar, Var, Prog(..), Prim(..), NumPrim(..), IntPrim(..), FloatPrim(..), ScalarPrim(..), BoolPrim(..), OtherPrim(..) )
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S

import Data.Array.Accelerate                                    as A hiding ( (++) )
import Data.Array.Accelerate.AST                                ( PrimFun(..) )
import Data.Array.Accelerate.Smart                              ( tup2, tup3, tup4, Exp(Exp), PreExp(PrimApp) )
import qualified Data.Array.Accelerate.AST                      as AST
import qualified Data.Array.Accelerate.Type                     as T
import qualified Data.Array.Accelerate.Array.Sugar              as Sugar

import Data.Dynamic                                             ( Typeable, Dynamic, fromDynamic, toDyn )
import Data.Map                                                 as M
import Prelude                                                  as P hiding ( exp )
import Text.PrettyPrint.GenericPretty                           ( Out(doc) )
import Text.Printf

dbgtrace :: String -> a -> a
dbgtrace =
  if dbg >= 5
  then maybtrace
  else \ _s x -> x


------------------------------------------------------------------------------------------

-- INCOMPLETE: In several places we have an incomplete pattern match
-- due to no Elt instances for C types: [2013.08.09]
#define CTYERR error "DynamicAcc: Could not handle CType, it is not in Elt yet!"
#define INSERT_CTY_ERR_CASES \
  TCFloat  -> CTYERR; \
  TCDouble -> CTYERR; \
  TCShort  -> CTYERR; \
  TCInt    -> CTYERR; \
  TCLong   -> CTYERR; \
  TCLLong  -> CTYERR; \
  TCUShort  -> CTYERR; \
  TCUInt    -> CTYERR; \
  TCULong   -> CTYERR; \
  TCULLong  -> CTYERR; \
  TCChar    -> CTYERR; \
  TCSChar   -> CTYERR; \
  TCUChar   -> CTYERR; \

--------------------------------------------------------------------------------
-- AST Representations
--------------------------------------------------------------------------------

-- TODO: make these pairs that keep around some printed rep for debugging purposes in
-- the case of a downcast error.  Also make them newtypes!
--
-- TODO: add the S.Type itself to each of these.
--
data SealedExp = SealedExp
  { expTy       :: S.Type
  , expDyn      :: Dynamic
  }
  deriving Show

data SealedFun = SealedFun
  { funTyIn     :: [S.Type]
  , funTyOut    :: S.Type
  , funDyn      :: Dynamic
  } deriving Show

data SealedAcc = SealedAcc
  { arrTy       :: ArrTy
  , accDyn      :: Dynamic
  }
  deriving Show

data ArrTy = ArrTy
  { eltTy       :: S.Type
  , ndims       :: Int
  }
  deriving Show

-- newtype SealedSlice = SealedSlice Dynamic deriving Show

sealExp :: forall a. (Elt a, Typeable a) => A.Exp a -> SealedExp
sealExp x = SealedExp ety (toDyn x)
 where
  ety = expType (undefined :: AST.Exp () a)

sealFun1 :: forall a b. (Elt a, Elt b) => (A.Exp a -> A.Exp b) -> SealedFun
sealFun1 f = SealedFun [ta] tb (toDyn f)
  where
    ta = expType (undefined :: AST.Exp () a)
    tb = expType (undefined :: AST.Exp () b)

sealAcc :: (Arrays a, Typeable a) => Acc a -> SealedAcc
sealAcc x =
  dbgtrace (" ** Creating arrTy: "++show ty0++" for "++show x) $
  SealedAcc (ArrTy elty dims) (toDyn x)
 where
  ty0@(TArray dims elty) = progType $ phase1 $ phase0 x

-- sealSlice :: (Typeable s) => s -> SealedSlice
-- sealSlice = SealedSlice . toDyn

-- | Cast a sealed expression into a statically typed one.  This may
-- fail with an exception.
downcastE :: forall a . Typeable a => SealedExp -> A.Exp a
downcastE (SealedExp _ d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
      error$"Attempt to unpack SealedExp "++show d
         ++ ", expecting type Exp "++ show (toDyn (unused::a))

downcastF1
    :: forall a b. (Typeable a, Typeable b)
    => SealedFun
    -> (A.Exp a -> A.Exp b)
downcastF1 (SealedFun _ _ d) =
  case fromDynamic d of
    Just e      -> e
    Nothing     -> error $ printf "Attempt to unpack SealedFun %s, expecting type Exp %s"
                              (show d) (show (toDyn (unused :: a -> b)))

downcastF2
    :: forall a b c. (Typeable a, Typeable b, Typeable c)
    => SealedFun
    -> (A.Exp a -> A.Exp b -> A.Exp c)
downcastF2 (SealedFun _ _ d) =
  case fromDynamic d of
    Just e      -> e
    Nothing     -> error $ printf "Attempt to unpack SealedFun %s, expecting type Exp %s"
                              (show d) (show (toDyn (unused :: a -> b -> c)))

unused :: a
unused = error "This dummy value should not be used"

-- | Cast a sealed array expression into a statically typed one.  This
-- may fail with an exception.
downcastA :: forall a . Typeable a => SealedAcc -> Acc a
downcastA (SealedAcc _ d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
       error$"Attempt to unpack SealedAcc "++show d
          ++ ", expecting type Acc "++ show (toDyn (unused::a))
-- TODO: could expose the Maybe here for the variants we export.


-- | Convert a `SimpleAcc` constant into a fully-typed (but sealed) Accelerate one.
constantE :: Const -> SealedExp

#define SEALIT(pat) pat x -> sealExp (A.constant x);
constantE c =
  case c of {
    SEALIT(I) SEALIT(I8) SEALIT(I16) SEALIT(I32) SEALIT(I64)
    SEALIT(W) SEALIT(W8) SEALIT(W16) SEALIT(W32) SEALIT(W64)
    SEALIT(F) SEALIT(D)
    SEALIT(B)
    SEALIT(CS) SEALIT(CI) SEALIT(CL) SEALIT(CLL)
    SEALIT(CUS) SEALIT(CUI) SEALIT(CUL) SEALIT(CULL)
    SEALIT(C) SEALIT(CC) SEALIT(CSC) SEALIT(CUC)
    SEALIT(CF) SEALIT(CD)
    Tup [] -> sealExp $ A.constant ();
    Tup ls -> convertExp (S.ETuple$ P.map S.EConst ls)
  }

--------------------------------------------------------------------------------
-- Type representations
--------------------------------------------------------------------------------

-- | We enhance "Data.Array.Accelerate.Type.TupleType" with Elt constraints.
--
--   Further, we attempt to model SURFACE tuples here, not their binary-tree encoding.
--
-- TODO: Get rid of SingleTuple and possible just use the NilTup/SnocTup rep.
--
data EltTuple a where
  UnitTuple     :: EltTuple ()

  SingleTuple   :: Elt a
                => T.ScalarType a
                -> EltTuple a

  Tuple2        :: (Elt a, Elt b)
                => EltTuple a -> EltTuple b
                -> EltTuple (a, b)

  Tuple3        :: (Elt a, Elt b, Elt c)
                => EltTuple a -> EltTuple b -> EltTuple c
                -> EltTuple (a, b, c)

  Tuple4        :: (Elt a, Elt b, Elt c, Elt d)
                => EltTuple a -> EltTuple b -> EltTuple c -> EltTuple d
                -> EltTuple (a, b, c, d)

 deriving Typeable

-- | This GADT allows monomorphic value to carry a type inside.
data SealedEltTuple where
  SealedEltTuple :: (Typeable a, Elt a) =>
                    EltTuple a -> SealedEltTuple

-- | This is a bottle in which to store a type that satisfyies the Array class.
data SealedArrayType where
  -- Do we care about the ArrayElt class here?
  SealedArrayType :: Arrays a => Phantom a -> SealedArrayType

-- | Tuples of arrays rather than scalar `Elt`s.
data ArrTuple a where
  UnitTupleA   ::                                                     ArrTuple ()
  SingleTupleA :: Arrays a             => Phantom a                -> ArrTuple a
  PairTupleA   :: (Arrays a, Arrays b) => ArrTuple a -> ArrTuple b -> ArrTuple (a, b)

-- TODO: CAN WE PHASE OUT SealedArrayType in favor of SealedArrTuple?
data SealedArrTuple where
  SealedArrTuple :: ArrTuple a -> SealedArrTuple

-- | Accelerate shape types, sealed up.
data SealedShapeType where
  -- Do we care about the ArrayElt class here?
  SealedShapeType :: Shape sh => Phantom sh -> SealedShapeType

data SealedSliceType where
  SealedSliceType :: (Sugar.Slice sl, Elt sl) => Phantom sl -> SealedSliceType
  deriving Typeable

-- data SliceIndex ix slice coSlice sliceDim where
--   SliceNil   :: SliceIndex () () () ()
--   SliceAll   ::
--    SliceIndex ix slice co dim -> SliceIndex (ix, ()) (slice, Int) co (dim, Int)
--   SliceFixed ::
--    SliceIndex ix slice co dim -> SliceIndex (ix, Int) slice (co, Int) (dim, Int)


-- | Convert the runtime, monomorphic type representation into a sealed
-- container with the true Haskell type inside.
--
scalarTypeD :: Type -> SealedEltTuple
scalarTypeD ty =
  case ty of
    TInt    -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int)
    TInt8   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int8)
    TInt16  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int16)
    TInt32  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int32)
    TInt64  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int64)
    TWord   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word)
    TWord8  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word8)
    TWord16 -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word16)
    TWord32 -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word32)
    TWord64 -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word64)
    TFloat  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Float)
    TDouble -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Double)
    TBool   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Bool)
    TChar   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Char)

    INSERT_CTY_ERR_CASES

    -- Here we have a problem... we've lost the surface tuple
    -- representation.... What canonical tuple representation do we use?
    TTuple []   -> SealedEltTuple UnitTuple
    TTuple [_]  -> error "scalarTypeD: singleton tuple" -- scalarTypeD sing  TLM: should not happen

    TTuple [a,b]
      | SealedEltTuple (ta :: EltTuple a) <- scalarTypeD a
      , SealedEltTuple (tb :: EltTuple b) <- scalarTypeD b
      -> SealedEltTuple $ Tuple2 ta tb

    TTuple [a,b,c]
      | SealedEltTuple (ta :: EltTuple a) <- scalarTypeD a
      , SealedEltTuple (tb :: EltTuple b) <- scalarTypeD b
      , SealedEltTuple (tc :: EltTuple c) <- scalarTypeD c
      -> SealedEltTuple $ Tuple3 ta tb tc

    TTuple [a,b,c,d]
      | SealedEltTuple (ta :: EltTuple a) <- scalarTypeD a
      , SealedEltTuple (tb :: EltTuple b) <- scalarTypeD b
      , SealedEltTuple (tc :: EltTuple c) <- scalarTypeD c
      , SealedEltTuple (td :: EltTuple d) <- scalarTypeD d
      -> SealedEltTuple $ Tuple4 ta tb tc td

    TArray {} -> error$"scalarTypeD: expected scalar type, got "++show ty

-- | Almost dependent types!  Dynamically construct a type in a bottle
-- that is isomorphic to an input value.  It can be opened up and used
-- as a goal type when repacking array data or returning an Acc
-- computation.
arrayTypeD :: Type -> SealedArrayType
-- TODO: Fix this to take ArrTy
arrayTypeD (TArray ndim elty) =
  case shapeTypeD ndim of
    SealedShapeType (_ :: Phantom sh) ->
#define ATY(t1,t2) t1 -> SealedArrayType (Phantom :: Phantom (Array sh t2));
     case elty of {
       ATY(TInt,Int) ATY(TInt8,Int8) ATY(TInt16,Int16) ATY(TInt32,Int32) ATY(TInt64,Int64)
       ATY(TWord,Word) ATY(TWord8,Word8) ATY(TWord16,Word16) ATY(TWord32,Word32) ATY(TWord64,Word64)
       ATY(TFloat,Float) ATY(TDouble,Double)
       ATY(TChar,Char) ATY(TBool,Bool)

       INSERT_CTY_ERR_CASES

       TTuple _ls -> (case scalarTypeD elty of
                      SealedEltTuple (_et :: EltTuple etty) ->
                       SealedArrayType (Phantom:: Phantom(Array sh etty)));
       TArray _ _ -> error$"arrayTypeD: nested array type, not allowed in Accelerate: "++show(TArray ndim elty)
     }
arrayTypeD x@(TTuple _) = error$"arrayTypeD: does not handle tuples of arrays yet: "++show x
arrayTypeD oth = error$"arrayTypeD: expected array type, got "++show oth


arrayTypeD' :: ArrTy -> SealedArrayType
arrayTypeD' (ArrTy t d) = arrayTypeD (TArray d t)


-- | Construct a Haskell type from an Int!  Why not?!
--
shapeTypeD :: Int -> SealedShapeType
shapeTypeD n | n < 0 = error "shapeTypeD: Cannot take a negative number!"
shapeTypeD 0 = SealedShapeType (Phantom :: Phantom Z)
shapeTypeD n
  | SealedShapeType (Phantom :: Phantom sh) <- shapeTypeD (n-1)
  = SealedShapeType (Phantom :: Phantom (sh :. Int))


-- | Dynamically construct an inhabitant of the Slice class.
--
sliceTypeD :: S.SliceType -> SealedSliceType
sliceTypeD []
  = SealedSliceType (Phantom :: Phantom Z)

sliceTypeD (S.Fixed : sl)
  | SealedSliceType (_ :: Phantom sl) <- sliceTypeD sl
  = SealedSliceType (Phantom :: Phantom (sl :. Int))

sliceTypeD (S.All : sl)
  | SealedSliceType (_ :: Phantom sl) <- sliceTypeD sl
  = SealedSliceType (Phantom :: Phantom (sl :. All))


--------------------------------------------------------------------------------
-- AST Construction
--------------------------------------------------------------------------------

-- | Convert a closed `SimpleAcc` expression (no free vars) into a fully-typed
--   (but sealed) Accelerate expression.
--
convertAcc :: S.AExp -> SealedAcc
convertAcc = convertOpenAcc emptyEnvPack

convertOpenAcc :: EnvPack -> S.AExp -> SealedAcc
convertOpenAcc env@(EnvPack _ _ mp) ae =
  let getAVr v = let (_,sa) = mp # v in expectAVar sa
  in
  case ae of
    S.Vr vr                     -> getAVr vr
    S.Use accarr                -> useD accarr
    S.Unit e                    -> unitD env e
    S.Map f a                   -> mapD env f a
    S.ZipWith f a b             -> zipWithD env f a b
    S.Generate sh f             -> generateD env sh f
    S.Backpermute sh p a        -> backpermuteD env sh p a
    S.Fold f z a                -> foldD env f z a

--    S.Replicate slc inE inA ->
--      replicateD (sliceTypeD slc) (convertOpenExp env inE) (getAVr inA)

    _ -> error$"FINISHME/DynamicAcc: convertOpenAcc: unhandled array operation: " ++show ae


-- Dynamic conversion of array operations
-- --------------------------------------

unitD :: EnvPack -> S.Exp -> SealedAcc
unitD env@(EnvPack _ _ mp) e
  | SealedEltTuple (_ :: EltTuple e)    <- scalarTypeD te
  = let
        e' :: Exp e
        e' = downcastE (convertOpenExp env e)
    in
    sealAcc $ A.unit e'
  where
    typeEnv     = M.map P.fst mp
    te          = S.recoverExpType typeEnv e


-- | Dynamically-typed variant of `Data.Array.Accelerate.use`.  However, this
-- version is less powerful, it only takes a single, logical array, not a tuple
-- of arrays.
--
useD :: S.AccArray -> SealedAcc
useD arr
  | SealedArrayType (Phantom :: Phantom a) <- arrayTypeD (S.accArrayToType arr)
  = sealAcc $ A.use (repackAcc (unused:: Acc a) [arr])

-- | Dynamically-typed variant of `Data.Array.Accelerate.generate`.
--
-- TLM: Backend kit doesn't represent indices properly, so we need can't use the
--      usual 'convertFun1'. Instead, we need to insert a type conversion from
--      indices to tuples manually.
--
generateD :: EnvPack -> S.Exp -> S.Fun1 S.Exp -> SealedAcc
generateD env@(EnvPack _ _ mp) sh f@(S.Lam1 (vix,tix) body)
  | SealedShapeType (_ :: Phantom sh)   <- shapeTypeD dim
  , SealedEltTuple  (_ :: EltTuple e)   <- scalarTypeD te
  = let
        f' :: Exp sh -> Exp e
        f' x =
          let ix    = indexToTup tix $ sealExp x
              env'  = extendE vix tix ix env
          in
          downcastE $ convertOpenExp env' body

        sh' :: Exp sh
        sh' = downcastE (tupToIndex tsh (convertOpenExp env sh))
    in
    sealAcc $ A.generate sh' f'
  where
    typeEnv     = M.map P.fst mp
    dim         = shapeTyLen tsh
    tsh         = S.recoverExpType typeEnv sh
    te          = S.recoverFun1Type typeEnv f

mapD :: EnvPack -> S.Fun1 S.Exp -> S.Var -> SealedAcc
mapD (EnvPack _ _ mp) f avar
  | SealedShapeType (_ :: Phantom sh)   <- shapeTypeD dim
  , SealedEltTuple  (_ :: EltTuple a)   <- scalarTypeD ta
  , SealedEltTuple  (_ :: EltTuple b)   <- scalarTypeD tb
  = let
        f' :: Exp a -> Exp b
        f' = downcastF1 (convertFun1 f tb)

        acc :: Acc (Array sh a)
        acc = downcastA (expectAVar sa)
    in
    sealAcc $ A.map f' acc
  where
    typeEnv             = M.map P.fst mp
    (arrTy, sa)         = mp # avar
    TArray dim ta       = arrTy
    tb                  = S.recoverFun1Type typeEnv f

zipWithD :: EnvPack -> S.Fun2 S.Exp -> S.Var -> S.Var -> SealedAcc
zipWithD (EnvPack _ _ mp) f avar1 avar2
  | SealedShapeType (_ :: Phantom sh)   <- shapeTypeD dim
  , SealedEltTuple  (_ :: EltTuple a)   <- scalarTypeD ta
  , SealedEltTuple  (_ :: EltTuple b)   <- scalarTypeD tb
  , SealedEltTuple  (_ :: EltTuple c)   <- scalarTypeD tc
  = let
        f' :: Exp a -> Exp b -> Exp c
        f' = downcastF2 (convertFun2 f tc)

        acc1 :: Acc (Array sh a)
        acc1 = downcastA (expectAVar sa1)

        acc2 :: Acc (Array sh b)
        acc2 = downcastA (expectAVar sa2)
    in
    sealAcc $ A.zipWith f' acc1 acc2
  where
    typeEnv                     = M.map P.fst mp
    (TArray dim ta, sa1)        = mp # avar1
    (TArray _   tb, sa2)        = mp # avar2
    tc                          = S.recoverFun2Type typeEnv f


{--
replicateD :: EnvPack -> S.SliceType -> S.Exp -> S.Var -> SealedAcc
replicateD env@(EnvPack _ _ mp) sliceIndex slix avar
  | SealedSliceType (_ :: Phantom slix)         <- sliceTypeD sliceIndex
  , SealedEltTuple  (_ :: EltTuple slix)        <- scalarTypeD tslix
  , SealedEltTuple  (_ :: EltTuple a)           <- scalarTypeD ta
  = let
        slix' :: Exp slix
        slix' = downcastE (convertOpenExp env slix)

        acc :: Acc (Array (Sugar.SliceShape slix) a)
        acc = downcastA (expectAVar sa)
    in
    sealAcc $ A.replicate slix' acc
  where
    typeEnv             = M.map P.fst mp
    (TArray dim ta, sa) = mp # avar
    tslix               = S.recoverExpType typeEnv slix
--}

backpermuteD :: EnvPack -> S.Exp -> S.Fun1 S.Exp -> S.Var -> SealedAcc
backpermuteD env@(EnvPack _ _ mp) sh' (S.Lam1 (vix,tix) body) avar
  | SealedShapeType (_ :: Phantom sh)   <- shapeTypeD dim
  , SealedShapeType (_ :: Phantom sh')  <- shapeTypeD dim'
  , SealedEltTuple  (_ :: EltTuple e)   <- scalarTypeD ta
  = let
        sh'' :: Exp sh'
        sh'' = downcastE (tupToIndex tix (convertOpenExp env sh'))

        p' :: Exp sh' -> Exp sh
        p' x =
          let ix'       = indexToTup tix $ sealExp x
              env'      = extendE vix tix ix' env
          in
          downcastE $ tupToIndex tix (convertOpenExp env' body)

        acc :: Acc (Array sh e)
        acc = downcastA (expectAVar sa)
    in
    sealAcc $ A.backpermute sh'' p' acc
  where
    typeEnv             = M.map P.fst mp
    (TArray dim ta, sa) = mp # avar
    dim'                = shapeTyLen tix


foldD :: EnvPack -> S.Fun2 S.Exp -> S.Exp -> S.Var -> SealedAcc
foldD env@(EnvPack _ _ mp) f z avar
  | SealedShapeType (_ :: Phantom sh)   <- shapeTypeD (dim-1)
  , SealedEltTuple  (_ :: EltTuple a)   <- scalarTypeD ta
  = let
        f' :: Exp a -> Exp a -> Exp a
        f' = downcastF2 (convertFun2 f ta)

        z' :: Exp a
        z' = downcastE (convertOpenExp env z)

        acc :: Acc (Array (sh :. Int) a)
        acc = downcastA (expectAVar sa)
    in
    sealAcc $ A.fold f' z' acc
  where
    (TArray dim ta, sa) = mp # avar


--------------------------------------------------------------------------------
-- TODO: These conversion functions could move to their own module:
--------------------------------------------------------------------------------

-- | Track the scalar, array environment, and combined, fast-access environment.
data EnvPack =
  EnvPack
    [(Var,Type)]
    [(AVar,Type)]
    (M.Map Var (Type, Either SealedExp SealedAcc))
 deriving Show

expectEVar :: Either SealedExp SealedAcc -> SealedExp
expectEVar (Left se)  = se
expectEVar (Right sa) = error$"expected scalar variable, got variable bound to: "++show sa

expectAVar :: Either SealedExp SealedAcc -> SealedAcc
expectAVar (Left se)  = error$"expected array variable, got variable bound to: "++show se
expectAVar (Right sa) = sa

emptyEnvPack :: EnvPack
emptyEnvPack = EnvPack [] [] M.empty

-- | New array binding
extendA :: AVar -> Type -> SealedAcc -> EnvPack -> EnvPack
extendA avr ty sld (EnvPack eS eA mp) =
  EnvPack eS ((avr,ty):eA)
          (M.insert avr (ty,Right sld) mp)

extendE :: Var -> Type -> SealedExp -> EnvPack -> EnvPack
extendE vr ty sld (EnvPack eS eA mp) =
  EnvPack ((vr,ty):eS) eA
          (M.insert vr (ty,Left sld) mp)


resealTup :: [(SealedEltTuple, SealedExp)] -> SealedExp
resealTup [] = sealExp$ A.constant ()

-- resealTup [(_,sing)] = sing

resealTup [(SealedEltTuple (_ :: EltTuple aty), a'),
           (SealedEltTuple (_ :: EltTuple bty), b')] =
    sealExp$ tup2 (downcastE a' :: Exp aty,
                   downcastE b' :: Exp bty)

resealTup [(SealedEltTuple (_ :: EltTuple aty), a),
           (SealedEltTuple (_ :: EltTuple bty), b),
           (SealedEltTuple (_ :: EltTuple cty), c)] =
    sealExp$ tup3 (downcastE a :: Exp aty,
                   downcastE b :: Exp bty,
                   downcastE c :: Exp cty)

resealTup [(SealedEltTuple (_ :: EltTuple aty), a),
           (SealedEltTuple (_ :: EltTuple bty), b),
           (SealedEltTuple (_ :: EltTuple cty), c),
           (SealedEltTuple (_ :: EltTuple dty), d)] =
    sealExp$ tup4 (downcastE a :: Exp aty,
                   downcastE b :: Exp bty,
                   downcastE c :: Exp cty,
                   downcastE d :: Exp dty)

resealTup components =
  error$ "resealTup: mismatched or unhandled tuple: "++show components


-- | Convert open scalar functions
--
convertFun1 :: S.Fun1 S.Exp -> S.Type -> SealedFun
convertFun1 = convertOpenFun1 emptyEnvPack

convertFun2 :: S.Fun2 S.Exp -> S.Type -> SealedFun
convertFun2 = convertOpenFun2 emptyEnvPack


-- | Convert open scalar functions
--
convertOpenFun1 :: EnvPack -> S.Fun1 S.Exp -> S.Type -> SealedFun
convertOpenFun1 env (S.Lam1 (va,ta) body) tb
  | SealedEltTuple (_ :: EltTuple a) <- scalarTypeD ta
  , SealedEltTuple (_ :: EltTuple b) <- scalarTypeD tb
  = let
        f :: A.Exp a -> A.Exp b
        f x =
          let x'   = sealExp x
              env' = extendE va ta x' env
          in
          downcastE $ convertOpenExp env' body
    in
    SealedFun [ta] tb (toDyn f)


convertOpenFun2 :: EnvPack -> S.Fun2 S.Exp -> S.Type -> SealedFun
convertOpenFun2 env (S.Lam2 (va,ta) (vb,tb) body) tc
  | SealedEltTuple (_ :: EltTuple a) <- scalarTypeD ta
  , SealedEltTuple (_ :: EltTuple b) <- scalarTypeD tb
  , SealedEltTuple (_ :: EltTuple c) <- scalarTypeD tc
  = let
        f :: A.Exp a -> A.Exp b -> A.Exp c
        f x y =
          let x'   = sealExp x
              y'   = sealExp y
              env' = extendE vb tb y' (extendE va ta x' env)    -- TLM: which order to push things in?
          in
          downcastE $ convertOpenExp env' body
    in
    SealedFun [ta,tb] tc (toDyn f)


-- | Convert a closed scalar expression
--
-- TLM: Note that SimpleAcc does not do what you would expect it to do. What is
--      a closed scalar expression in properly typed Accelerate, often needs to
--      be sealed with the environment ('convertOpenExp'). This seems wrong to
--      me...
--
convertExp :: S.Exp -> SealedExp
convertExp = convertOpenExp emptyEnvPack

-- | Convert an entire `SimpleAcc` expression into a fully-typed (but sealed) Accelerate one.
--   Requires a type environments for the (open) `SimpleAcc` expression:
--   one for free expression variables, one for free array variables.
--
convertOpenExp :: EnvPack -> S.Exp -> SealedExp
convertOpenExp ep@(EnvPack envE envA mp) ex
  = dbgtrace(printf " @ Converting exp %s with\n  env: %s\n  dynamic env: %s\n" (show ex) (show mp) (show (envE,envA)))
  $ dbgtrace(printf " @ Converted exp result: %s " (show result))
  $ result
  where
    cvtF1 :: S.Fun1 S.Exp -> S.Type -> SealedFun
    cvtF1 = convertOpenFun1 ep

    cvtE :: S.Exp -> SealedExp
    cvtE e =
      case e of
        S.EConst c              -> constantE c
        S.EVr var               -> let (_,se) = mp # var in expectEVar se
        S.ELet e1 e2            -> elet e1 e2
        S.EShape sh             -> eshape sh
        S.EShapeSize sh         -> eshapeSize sh
        S.EIndex ix             -> eindex ix
        S.EIndexScalar var ix   -> eindexScalar var ix
        S.ETupProject _ m n ix  -> prjT m n ix
        S.ETuple tup            -> etuple tup
        S.EPrimApp ty f xs      -> eprimApp ty f xs
        S.ECond p e1 e2         -> econd p e1 e2
        S.EWhile p f e          -> ewhile p f e

    -- Strip out the SealedExp/Acc bits leaving just the types
    typeEnv :: M.Map Var Type
    typeEnv = M.map P.fst mp

    result :: SealedExp
    result = cvtE ex

    -- Shapes and indices
    --
    eshape :: S.Var -> SealedExp
    eshape avar
      | SealedShapeType (_ :: Phantom sh) <- shapeTypeD dim
      , SealedEltTuple  (_ :: EltTuple e) <- scalarTypeD e
      = let arr :: Acc (Array sh e)
            arr = downcastA $ expectAVar sa
        in
        sealExp $ A.shape arr
      where
        (arrTy, sa)     = mp # avar
        TArray dim e    = arrTy

    eshapeSize :: S.Exp -> SealedExp
    eshapeSize _ = error "DynamicAcc.convertOpenExp: EShapeSize"

    eindex :: [S.Exp] -> SealedExp
    eindex _ = error "DynamicAcc.convertOpenExp: EIndex"

    -- Scalar let bindings
    --
    elet :: (Var, Type, S.Exp) -> S.Exp -> SealedExp
    elet (var, ty, bnd) body =
      let bnd'                  = cvtE bnd
          bodyTy                = scalarTypeD (S.recoverExpType (M.map P.fst m2) body)
          ep'@(EnvPack _ _ m2)  = extendE var ty bnd' ep
      in
      convertOpenExp ep' body

    -- Scalar conditionals
    --
    econd :: S.Exp -> S.Exp -> S.Exp -> SealedExp
    econd p e1 e2
      | SealedEltTuple (_ :: EltTuple e) <- scalarTypeD (S.recoverExpType typeEnv e1)
      = let p' :: Exp Bool
            p' = downcastE (cvtE p)

            e1', e2' :: Exp e
            e1' = downcastE (cvtE e1)
            e2' = downcastE (cvtE e2)
        in
        sealExp (p' A.? (e1', e2'))

    -- Here we run straight into our mismatch between the Acc and SimpleAcc
    -- treatment of shape types.
    --
    eindexScalar :: S.Var -> S.Exp -> SealedExp
    eindexScalar avar ix
      | SealedShapeType (_ :: Phantom sh) <- shapeTypeD dim
      , SealedEltTuple  (_ :: EltTuple e) <- scalarTypeD e
      = let ix' :: Exp sh
            ix' = downcastE $ tupToIndex (S.recoverExpType typeEnv ix) (cvtE ix)

            arr :: Acc (Array sh e)
            arr = downcastA $ expectAVar sa
        in
        sealExp $ arr A.! ix'
      where
        (arrTy, sa)     = mp # avar
        TArray dim e    = arrTy

    -- Scalar tuples
    --
    etuple :: [S.Exp] -> SealedExp
    etuple []   = constantE (Tup [])
    etuple [e]  = cvtE e
    etuple es   = resealTup
                $ P.map (\e -> (scalarTypeD (S.recoverExpType typeEnv e), cvtE e)) es

    -- Scalar tuple projection
    --
    -- FIXME: This is having a FLATTING effect, which isn't valid for surface tuples
    --
    prjT :: Int -> Int -> S.Exp -> SealedExp
    prjT ind len exp
      | dbgtrace (printf "ETupProject: ind=%d, len=%d, tup=%s\n" ind len (show exp)) False
      = undefined

      | SealedEltTuple (tup :: EltTuple tup) <- scalarTypeD tupTy
      = case tup of
          UnitTuple
            -> error "DynamicAcc.convertOpenExp: Tuple projection from unit"

          SingleTuple (_ :: T.ScalarType a)
            -> let exp' :: Exp a
                   exp' = downcastE $ cvtE exp
               in
               sealExp exp'

          Tuple2 (ta :: EltTuple a) (tb :: EltTuple b)
            -> let exp' :: Exp (a,b)
                   exp'  = downcastE $ cvtE exp
                   (a,b) = unlift exp'
               in
               sliceT [SealedEltTuple ta, SealedEltTuple tb]
                      [sealExp a, sealExp b]

          Tuple3 (ta :: EltTuple a) (tb :: EltTuple b) (tc :: EltTuple c)
            -> let exp' :: Exp (a,b,c)
                   exp'    = downcastE $ cvtE exp
                   (a,b,c) = unlift exp'
               in
               sliceT [SealedEltTuple ta, SealedEltTuple tb, SealedEltTuple tc]
                      [sealExp a, sealExp b, sealExp c]

          Tuple4 (ta :: EltTuple a) (tb :: EltTuple b) (tc :: EltTuple c) (td :: EltTuple d)
            -> let exp' :: Exp (a,b,c,d)
                   exp'      = downcastE $ cvtE exp
                   (a,b,c,d) = unlift exp'
               in
               sliceT [SealedEltTuple ta, SealedEltTuple tb, SealedEltTuple tc, SealedEltTuple td]
                      [sealExp a, sealExp b, sealExp c, sealExp d]

      where
        tupTy           = S.recoverExpType typeEnv exp
        sliceT ts es    = resealTup . P.take len . P.drop ind $ P.zip ts es

    -- Scalar iteration
    --
    ewhile :: S.Fun1 S.Exp -> S.Fun1 S.Exp -> S.Exp -> SealedExp
    ewhile p f e
      | te                               <- S.recoverExpType typeEnv e
      , SealedEltTuple (_ :: EltTuple e) <- scalarTypeD te
      = let p' :: Exp e -> Exp Bool
            p' = downcastF1 (cvtF1 p S.TBool)

            f' :: Exp e -> Exp e
            f' = downcastF1 (cvtF1 f te)

            e' :: Exp e
            e' = downcastE (cvtE e)
        in
        sealExp $ A.while p' f' e'

    -- Primitive function application.
    -- This is extremely painful.
    --
    eprimApp :: S.Type -> S.Prim -> [S.Exp] -> SealedExp
    eprimApp outTy op args
      | SealedEltTuple (SingleTuple (sa :: T.ScalarType a)) <- scalarTypeD inTy
      , SealedEltTuple (SingleTuple (sb :: T.ScalarType b)) <- scalarTypeD outTy
      = sealExp
      $ case op of
          NP f | T.NumScalarType t                      <- sb   -> num t f
          IP f | T.NumScalarType (T.IntegralNumType t)  <- sb   -> integral t f
          FP f | T.NumScalarType (T.FloatingNumType fa) <- sa
               , T.NumScalarType nb                     <- sb   -> floating fa nb f
          BP f | T.NonNumScalarType T.TypeBool{} <- sb          -> bool f
          SP f                                                  -> scalar sa sb f
          OP f                                                  -> other sa sb f
          _ -> error "DynamicAcc.convertOpenExp: inconsistent valuation"

      | otherwise
      = error "DynamicAcc.convertOpenExp: inconsistent valuation"
      where
        args'   = P.map cvtE args
        inTy    = S.recoverExpType typeEnv (head args)

        unary :: (Elt a, Elt b) => PrimFun (a -> b) -> Exp b
        unary f
          | [x] <- args'        = Exp $ f `PrimApp` downcastE x
          | otherwise           = error "DynamicAcc.convertOpenExp: inconsistent valuation"

        binary :: (Elt a, Elt b, Elt c) => PrimFun ((a,b) -> c) -> Exp c
        binary f
          | [x,y] <-  args'     = Exp $ f `PrimApp` tup2 (downcastE x, downcastE y)
          | otherwise           = error "DynamicAcc.convertOpenExp: inconsistent valuation"

        num :: Elt a => T.NumType a -> NumPrim -> Exp a
        num t Add = binary (PrimAdd t)
        num t Sub = binary (PrimSub t)
        num t Mul = binary (PrimMul t)
        num t Neg = unary  (PrimNeg t)
        num t Abs = unary  (PrimAbs t)
        num t Sig = unary  (PrimSig t)

        integral :: Elt a => T.IntegralType a -> IntPrim -> Exp a
        integral t Quot     = binary (PrimQuot t)
        integral t Rem      = binary (PrimRem t)
        integral t IDiv     = binary (PrimIDiv t)
        integral t Mod      = binary (PrimMod t)
        integral t BAnd     = binary (PrimBAnd t)
        integral t BOr      = binary (PrimBOr t)
        integral t BXor     = binary (PrimBXor t)
        integral t BNot     = unary  (PrimBNot t)
        integral t BShiftL  = binary (PrimBShiftL t)
        integral t BShiftR  = binary (PrimBShiftR t)
        integral t BRotateL = binary (PrimBRotateL t)
        integral t BRotateR = binary (PrimBRotateR t)

        floating :: (Elt a, Elt b) => T.FloatingType a -> T.NumType b -> FloatPrim -> Exp b
        floating ta nb f
          | T.FloatingNumType tb <- nb
          = case f of
              Recip       -> unary  (PrimRecip tb)
              Sin         -> unary  (PrimSin tb)
              Cos         -> unary  (PrimCos tb)
              Tan         -> unary  (PrimTan tb)
              Asin        -> unary  (PrimAsin tb)
              Acos        -> unary  (PrimAcos tb)
              Atan        -> unary  (PrimAtan tb)
              Asinh       -> unary  (PrimAsinh tb)
              Acosh       -> unary  (PrimAcosh tb)
              Atanh       -> unary  (PrimAtanh tb)
              ExpFloating -> unary  (PrimExpFloating tb)
              Sqrt        -> unary  (PrimSqrt tb)
              Log         -> unary  (PrimLog tb)
              FDiv        -> binary (PrimFDiv tb)
              FPow        -> binary (PrimFPow tb)
              LogBase     -> binary (PrimLogBase tb)
              Atan2       -> binary (PrimAtan2 tb)
              _           -> error "DynamicAcc.convertOpenExp: inconsistent valuation"

          | T.IntegralNumType tb <- nb
          = case f of
              Truncate    -> unary (PrimTruncate ta tb)
              Round       -> unary (PrimRound ta tb)
              Floor       -> unary (PrimFloor ta tb)
              Ceiling     -> unary (PrimCeiling ta tb)
              _           -> error "DynamicAcc.convertOpenExp: inconsistent valuation"

          | otherwise
          = error "DynamicAcc.convertOpenExp: inconsistent valuation"

        scalar :: (Elt a, Elt b) => T.ScalarType a -> T.ScalarType b -> ScalarPrim -> Exp b
        scalar sa sb f
          | T.NonNumScalarType T.TypeBool{} <- sb
          = case f of
              Lt   -> binary (PrimLt sa)
              Gt   -> binary (PrimGt sa)
              LtEq -> binary (PrimLtEq sa)
              GtEq -> binary (PrimGtEq sa)
              Eq   -> binary (PrimEq sa)
              NEq  -> binary (PrimNEq sa)
              _    -> error "DynamicAcc.convertOpenExp: inconsistent valuation"

          | otherwise
          = case f of
              Min  -> binary (PrimMin sb)
              Max  -> binary (PrimMax sb)
              _    -> error "DynamicAcc.convertOpenExp: inconsistent valuation"

        bool :: BoolPrim -> Exp Bool
        bool And = binary PrimLAnd
        bool Or  = binary PrimLOr
        bool Not = unary  PrimLNot

        other :: (Elt a, Elt b) => T.ScalarType a -> T.ScalarType b -> OtherPrim -> Exp b
        other sa sb f =
          case f of
            Ord
              | T.NonNumScalarType T.TypeChar{}                 <- sa
              , T.NumScalarType (T.IntegralNumType T.TypeInt{}) <- sb
              -> unary PrimOrd

            Chr
              | T.NumScalarType (T.IntegralNumType T.TypeInt{}) <- sa
              , T.NonNumScalarType T.TypeChar{}                 <- sb
              -> unary PrimChr

            BoolToInt
              | T.NonNumScalarType T.TypeBool{} <- sa
              , T.NumScalarType (T.IntegralNumType T.TypeInt{}) <- sb
              -> unary PrimBoolToInt

            FromIntegral
              | T.NumScalarType (T.IntegralNumType ta) <- sa
              , T.NumScalarType tb                     <- sb
              -> unary (PrimFromIntegral ta tb)

            _ -> error "DynamicAcc.convertOpenExp: inconsistent valuation"



-- | The SimpleAcc representation does NOT keep index types disjoint
-- from regular tuples.  To convert back to Acc we need to reassert
-- this distinction, which involves "casting" indices to tuples and
-- tuples to indices at the appropriate places.
indexToTup :: S.Type -> SealedExp -> SealedExp
indexToTup ty ex
  = dbgtrace (" -- starting indexToTup... ")
  $ dbgtrace (" -- indexTo tup, converting "++show (ty,ex)++" to "++ show res)
  $ res
  where
    res =
     case ty of
       TTuple [] -> sealExp (constant ())

       TTuple [TInt,TInt] ->
         let l,r :: Exp Int
             (Z :. l :. r) = unlift (downcastE ex :: Exp (Z :. Int :. Int))
             tup :: Exp (Int, Int)
             tup = lift (l, r)
         in sealExp tup

       TTuple [TInt,TInt,TInt] ->
         let a,b,c :: Exp Int
             (Z :. a :. b :. c) = unlift (downcastE ex :: Exp (Z :. Int :. Int :. Int))
             tup :: Exp (Int, Int, Int)
             tup = lift (a,b,c)
         in sealExp tup

-- FINISHME: Go up to tuple size 9.

       TTuple{}  -> error$ "indexToTup: tuple type not handled: "++show(ty,ex)
       TArray{}  -> error$ "indexToTup: expected tuple-of-scalar type, got: "++show ty
       _ ->
         case scalarTypeD ty of
           SealedEltTuple (t :: EltTuple elt) ->
             let
                 z :: Exp (Z :. elt)
                 z = downcastE ex
                 e' :: Exp (elt)
                 Z :. e' = unlift z
             in sealExp e'

-- | The inverse of `indexToTup`.  Takes the plain SimpleAcc TTuple of
-- TInt type as the first argument.
tupToIndex :: S.Type -> SealedExp -> SealedExp
tupToIndex ty ex =
    dbgtrace (" ~~ starting tupToIndex... ")$
    dbgtrace (" ~~ tupToIndex tup, converting "++show (ty,ex)++" to "++ show res) res
 where
 res =
  case ty of
    TTuple []  -> sealExp (constant Z)
    TTuple [a] -> error$ "tupToIndex: internal error, singleton tuple: "++show (ty,ex)

    TTuple [TInt,TInt] ->
      dbgtrace ("Converting tuple type to index type... "++show ty) $
          let l,r :: Exp Int
              (l,r) = unlift (downcastE ex :: Exp (Int,Int))
              ind' :: Exp (Z :. Int :. Int)
              ind' = lift (Z :. l :. r)
          in sealExp ind'

    TTuple [TInt,TInt,TInt] ->
      dbgtrace ("Converting tuple type to index type... "++show ty) $
          let a,b,c :: Exp Int
              (a,b,c) = unlift (downcastE ex :: Exp (Int,Int,Int))
              ind' :: Exp (Z :. Int :. Int :. Int)
              ind' = lift (Z :. a :. b :. c)
          in sealExp ind'

-- FINISHME: Go up to tuple size 9.

    TTuple{}  -> error$ "tupToIndex: unhandled tuple type: "++ show ty
    TArray{}  -> error$ "tupToIndex: expected tuple-of-scalar type, got: "++show ty
    _ ->
      case scalarTypeD ty of
        SealedEltTuple (t :: EltTuple elt) ->
          let
              z :: Z :. Exp elt
              z = Z :. ((downcastE ex) :: Exp elt)
              z' :: Exp (Z :. elt)
              z' = lift z
          in sealExp z'


tupTyToIndex = error "finish me"

shapeTyLen :: Type -> Int
shapeTyLen TInt        = 1
shapeTyLen (TTuple ls) | P.all (==TInt) ls = P.length ls
shapeTyLen ty = error $ "shapeTyLen: invalid shape type: "++show ty


-- | Convert an entire SimpleAcc `Prog` into a complete, closed, fully
-- typed Accelerate AST.  To use this AST, however, you will need to
-- know what type to downcast it to.
convertProg :: S.Prog () -> SealedAcc
convertProg S.Prog{progBinds,progResults} =
    dbgtrace ("CONVERTING whole prog "++show(doc progBinds)) $
    doBinds emptyEnvPack progBinds
  where
  doBinds env (S.ProgBind vr ty dec eith : rst) =
    dbgtrace (" dobinds of "++show (vr,ty,rst)++" "++show env) $
    case eith of
      Left ex  -> let se = convertOpenExp env ex
                      env' = extendE vr ty se env
                  in doBinds env' rst
      Right ae -> let sa = convertOpenAcc env ae
                      env' = extendA vr ty sa env
                  in doBinds env' rst
  doBinds (EnvPack _ _ mp) [] =
    case S.resultNames progResults of
      [resVr] -> expectAVar$ P.snd$ mp # resVr
      _ -> error$ "FINISHME/DynamicAcc: convertProg with multiple results: "++show progResults



--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance Show (EltTuple a) where
  show UnitTuple        = "()"
  show (SingleTuple st) = show st
  show (Tuple2 a b)     = "("++show a++","++show b++")"
  show (Tuple3 a b c)   = "("++show a++","++show b++","++show c++")"
  show (Tuple4 a b c d) = printf "(%s,%s,%s,%s)" (show a) (show b) (show c) (show d)

instance Show SealedEltTuple where
  show (SealedEltTuple x) = "Sealed:"++show x

instance Show SealedShapeType where
  show (SealedShapeType (Phantom :: Phantom sh)) =
    "Sealed:"++show (toDyn (unused::sh))

instance Show SealedArrayType where
  show (SealedArrayType (Phantom :: Phantom sh)) =
    "Sealed:"++show (toDyn (unused::sh))

--------------------------------------------------------------------------------

-- | For debugging purposes we should really never use Data.Map.!  This is an
-- alternative with a better error message.
(#) :: (Ord a1, Show a, Show a1) => M.Map a1 a -> a1 -> a
mp # k = case M.lookup k mp of
          Nothing -> error$"Map.lookup: key "++show k++" is not in map:\n  "++show mp
          Just x  -> x
