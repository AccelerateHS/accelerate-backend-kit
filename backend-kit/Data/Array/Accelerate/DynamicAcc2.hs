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
   constantE, useD, unitD, mapD, generateD, foldD, dbgtrace

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

import Control.Exception                                        ( assert )
import Data.Dynamic                                             ( Typeable, Dynamic, fromDynamic, toDyn, typeOf )
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

downcastF1 :: forall a b. (Typeable a, Typeable b) => SealedExp -> (A.Exp a -> A.Exp b)
downcastF1 (SealedExp _ d) =
  case fromDynamic d of
    Just e      -> e
    Nothing     -> error $ printf "Attempt to unpack SealedExp %s, expecting type Exp %s"
                              (show d) (show (toDyn (unused :: a -> b)))

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
data EltTuple a where
  UnitTuple   ::                                               EltTuple ()
  SingleTuple :: (Elt a)        => T.ScalarType a           -> EltTuple a
  PairTuple   :: (Elt a, Elt b) => EltTuple a -> EltTuple b -> EltTuple (a, b)
  ThreeTuple  :: (Elt a, Elt b, Elt c) => EltTuple a -> EltTuple b -> EltTuple c -> EltTuple (a, b, c)
 deriving Typeable
-- TODO: ^^ Get rid of SingleTuple and possible just use the NilTup/SnocTup rep.

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
  SealedSliceType :: (Sugar.Slice s, Elt s) => Phantom s -> SealedSliceType
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
    TTuple []      -> SealedEltTuple UnitTuple
    TTuple [sing]  -> scalarTypeD sing
    TTuple [x,y]   ->
        case (scalarTypeD x, scalarTypeD y) of
        (SealedEltTuple (et1 :: EltTuple a),
         SealedEltTuple (et2 :: EltTuple b)) ->
          SealedEltTuple$ PairTuple et1 et2

    TTuple [x,y,z]   ->
        case (scalarTypeD x, scalarTypeD y, scalarTypeD z) of
        (SealedEltTuple (et1),
         SealedEltTuple (et2),
         SealedEltTuple (et3)) ->
          SealedEltTuple$ ThreeTuple et1 et2 et3

    TTuple (hd:tl) ->
      error ("scalarTypeD: unifinished: "++show ty) $
      case (scalarTypeD hd, scalarTypeD (TTuple tl)) of
        (SealedEltTuple (et1 :: EltTuple a),
         SealedEltTuple (et2 :: EltTuple b)) ->
          SealedEltTuple$ PairTuple et1 et2
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

       TTuple ls -> (case scalarTypeD elty of
                      SealedEltTuple (et :: EltTuple etty) ->
                       SealedArrayType (Phantom:: Phantom(Array sh etty)));
       TArray _ _ -> error$"arrayTypeD: nested array type, not allowed in Accelerate: "++show(TArray ndim elty)
     }
arrayTypeD x@(TTuple _) = error$"arrayTypeD: does not handle tuples of arrays yet: "++show x
arrayTypeD oth = error$"arrayTypeD: expected array type, got "++show oth


arrayTypeD' :: ArrTy -> SealedArrayType
arrayTypeD' (ArrTy t d) = arrayTypeD (TArray d t)

-- | Construct a Haskell type from an Int!  Why not?
shapeTypeD :: Int -> SealedShapeType
shapeTypeD 0 = SealedShapeType (Phantom :: Phantom Z)
shapeTypeD n | n < 0 = error "shapeTypeD: Cannot take a negative number!"
shapeTypeD n =
  case shapeTypeD (n-1) of
    SealedShapeType (Phantom :: Phantom sh) ->
      SealedShapeType (Phantom :: Phantom (sh :. Int))


-- | Dynamically construct an inhabitant of the Slice class.
sliceTypeD :: S.SliceType -> SealedSliceType
sliceTypeD [] = SealedSliceType (Phantom :: Phantom Z)
sliceTypeD (S.Fixed:rst) =
  case sliceTypeD rst of
    SealedSliceType (_ :: Phantom slc) ->
      SealedSliceType (Phantom :: Phantom (slc :. Int))
sliceTypeD (S.All:rst) =
  case sliceTypeD rst of
    SealedSliceType (_ :: Phantom slc) ->
      SealedSliceType (Phantom :: Phantom (slc :. All))

--------------------------------------------------------------------------------
-- AST Construction
--------------------------------------------------------------------------------


-- | Dynamically typed variant of `Data.Array.Accelerate.unit`.
unitD :: SealedEltTuple -> SealedExp -> SealedAcc
unitD elt exp =
  dbgtrace (" ** starting unitD: "++show (elt,exp)) $
  case elt of
    SealedEltTuple (t :: EltTuple et) ->
      case t of
        UnitTuple -> sealAcc$ unit$ constant ()
        SingleTuple (_ :: T.ScalarType s) ->
          sealAcc$ unit (downcastE exp :: A.Exp  s)
        PairTuple (_ :: EltTuple l) (_ :: EltTuple r) ->
          sealAcc$ unit (downcastE exp :: A.Exp  (l,r))
        ThreeTuple (_ :: EltTuple a) (_ :: EltTuple b) (_ :: EltTuple c) ->
          sealAcc$ unit (downcastE exp :: A.Exp  (a,b,c))

-- | Dynamically-typed variant of `Data.Array.Accelerate.use`.  However, this version
-- is less powerful, it only takes a single, logical array, not a tuple of arrays.
useD :: S.AccArray -> SealedAcc
useD arr =
  case sty of
    SealedArrayType (Phantom :: Phantom aT) ->
      sealAcc$ A.use$
      repackAcc (unused::Acc aT) [arr]
 where
   dty = S.accArrayToType arr
   sty = arrayTypeD dty

generateD :: SealedExp -> (SealedExp -> SealedExp) ->
        S.Type -> SealedAcc
generateD indSealed bodfn outArrTy =
  dbgtrace (" ** starting generateD fun: outArrTy "++show (outArrTy)) $
      let (TArray dims outty) = outArrTy in
       case (shapeTypeD dims, scalarTypeD outty) of
         (SealedShapeType (_ :: Phantom shp),
          SealedEltTuple (outET :: EltTuple outT)) ->
          let
            rawfn :: Exp shp -> Exp outT
            rawfn x =
              dbgtrace (" ** Inside generate scalar fun, downcasting bod "++
                     show (bodfn (sealExp x))++" to "++ show (typeOf (undefined::outT))) $
              downcastE (bodfn (sealExp x))
            dimE :: Exp shp
            dimE = dbgtrace (" ** Generate: downcasting dim "++show indSealed++" Expecting Z-based index of dims "++show dims) $
                   downcastE indSealed
            acc = A.generate dimE rawfn
          in
           dbgtrace (" ** .. Body of generateD: raw acc: "++show acc) $
           sealAcc acc


mapD :: (SealedExp -> SealedExp) -> SealedAcc -> S.Type -> SealedAcc
mapD bodfn sealedInArr outElmTy =
      let (ArrTy inty dims) = arrTy sealedInArr
          newAty = arrayTypeD (TArray dims outElmTy)
      in
       -- TODO: Do we really need outElmTy here?
       case (shapeTypeD dims, scalarTypeD inty, scalarTypeD outElmTy) of
         (SealedShapeType (_ :: Phantom shp),
          SealedEltTuple (inET  :: EltTuple inT),
          SealedEltTuple (outET :: EltTuple outT)) ->
          let
            rawfn :: Exp inT -> Exp outT
            rawfn x = downcastE (bodfn (sealExp x))
            realIn :: Acc (Array shp inT)
            realIn = downcastA sealedInArr
          in
           -- Here we suffer PAIN to recover the Elt/Typeable instances:
           case (inET, outET) of
             (UnitTuple,     UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (PairTuple _ _, UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (ThreeTuple {}, UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (UnitTuple,     SingleTuple _) -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, SingleTuple _) -> sealAcc $ A.map rawfn realIn
             (PairTuple _ _, SingleTuple _) -> sealAcc $ A.map rawfn realIn
             (ThreeTuple {}, SingleTuple _) -> sealAcc $ A.map rawfn realIn
             (UnitTuple,     PairTuple _ _) -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, PairTuple _ _) -> sealAcc $ A.map rawfn realIn
             (PairTuple _ _, PairTuple _ _) -> sealAcc $ A.map rawfn realIn
             (ThreeTuple {}, PairTuple _ _) -> sealAcc $ A.map rawfn realIn
             (UnitTuple,     ThreeTuple {}) -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, ThreeTuple {}) -> sealAcc $ A.map rawfn realIn
             (PairTuple _ _, ThreeTuple {}) -> sealAcc $ A.map rawfn realIn
             (ThreeTuple {}, ThreeTuple {}) -> sealAcc $ A.map rawfn realIn

zipWithD :: (SealedExp -> SealedExp -> SealedExp) -> SealedAcc -> SealedAcc ->
            S.Type -> S.Type  -> S.Type -> SealedAcc
zipWithD bodfn sealedInArr1 sealedInArr2 inArrTy1 inArrTy2 outElmTy =
  error "FINISHME/DynamicAcc - zipWithD"


replicateD :: SealedSliceType -> SealedExp -> SealedAcc -> SealedAcc
replicateD slc exp arr =
  case (slc) of  -- , scalarTypeD (expTy exp)
    (SealedSliceType (_::Phantom slc)) ->
--     SealedEltTuple (inET  :: EltTuple inT) ) ->
     let e :: Exp slc
         e = error "FINISHME/DynamicAcc - replicateD"
--         _ = A.replicate e
     in
      error "FINISHME/DynamicAcc - replicateD"

foldD :: (SealedExp -> SealedExp -> SealedExp) -> SealedExp -> SealedAcc ->
         S.Type -> SealedAcc
foldD bodfn initE sealedInArr inArrTy =
      let (TArray dims inty) = inArrTy
          -- Knock off one dimension:
          newAty = arrayTypeD (TArray (dims - 1) inty)
      in
       case (shapeTypeD (dims - 1), scalarTypeD inty) of
         (SealedShapeType (_ :: Phantom shp),
          SealedEltTuple (inET  :: EltTuple inT)) ->
           let
               rawfn :: Exp inT -> Exp inT -> Exp inT
               rawfn x y = downcastE (bodfn (sealExp x) (sealExp y))
               realIn :: Acc (Array (shp :. Int) inT)
               realIn = downcastA sealedInArr
               init :: Exp inT
               init = downcastE initE
           in
            case inET of
              (UnitTuple    )     -> sealAcc $ A.fold rawfn init realIn
              (SingleTuple _)     -> sealAcc $ A.fold rawfn init realIn
              (PairTuple _ _)     -> sealAcc $ A.fold rawfn init realIn
              (ThreeTuple _ _ _)  -> sealAcc $ A.fold rawfn init realIn


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

type AENV0 = ()


resealTup :: [(SealedEltTuple, SealedExp)] -> SealedExp
resealTup [] = sealExp$ A.constant ()

resealTup [(_,sing)] = sing

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
convertOpenFun1 :: S.Fun1 S.Exp -> EnvPack -> SealedExp -> SealedExp
convertOpenFun1 (S.Lam1 (var,ty) body) env x =
  convertOpenExp (extendE var ty x env) body

convertOpenFun2 :: S.Fun2 S.Exp -> EnvPack -> SealedExp -> SealedExp -> SealedExp
convertOpenFun2 (S.Lam2 (var1,ty1) (var2,ty2) body) env x1 x2 =
  convertOpenExp (extendE var2 ty2 x2 (extendE var1 ty1 x1 env)) body

-- | Convert a closed scalar expression
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
    cvtF1 :: S.Fun1 S.Exp -> SealedExp -> SealedExp
    cvtF1 f = convertOpenFun1 f ep

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
        S.ETupProject m n ix    -> prjT m n ix
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

          PairTuple (ta :: EltTuple a) (tb :: EltTuple b)
            -> let exp' :: Exp (a,b)
                   exp'  = downcastE $ cvtE exp
                   (a,b) = unlift exp'
               in
               sliceT [SealedEltTuple ta, SealedEltTuple tb]
                      [sealExp a, sealExp b]

          ThreeTuple (ta :: EltTuple a) (tb :: EltTuple b) (tc :: EltTuple c)
            -> let exp' :: Exp (a,b,c)
                   exp'    = downcastE $ cvtE exp
                   (a,b,c) = unlift exp'
               in
               sliceT [SealedEltTuple ta, SealedEltTuple tb, SealedEltTuple tc]
                      [sealExp a, sealExp b, sealExp c]
      where
        tupTy           = S.recoverExpType typeEnv exp
        sliceT ts es     = resealTup . P.take len . P.drop ind $ P.zip ts es

    -- Scalar iteration
    --
    ewhile :: S.Fun1 S.Exp -> S.Fun1 S.Exp -> S.Exp -> SealedExp
    ewhile p f e
      | SealedEltTuple (_ :: EltTuple e) <- scalarTypeD (S.recoverExpType typeEnv e)
      = let p' :: Exp e -> Exp Bool
            p' = downcastF1 (cvtF1 p undefined)

            f' :: Exp e -> Exp e
            f' = downcastF1 (cvtF1 f undefined)

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
indexToTup ty ex =
  dbgtrace (" -- starting indexToTup... ")$
  dbgtrace (" -- indexTo tup, converting "++show (ty,ex)++" to "++ show res)
   res
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

       TTuple ls -> error$ "indexToTup: tuple type not handled: "++show(ty,ex)
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

    TTuple _ -> error$"tupToIndex: unhandled tuple type: "++ show ty

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

convertAcc :: S.AExp -> SealedAcc
convertAcc = convertOpenAcc emptyEnvPack

-- | Convert a closed `SimpleAcc` expression (no free vars) into a fully-typed (but
-- sealed) Accelerate one.
convertOpenAcc :: EnvPack -> S.AExp -> SealedAcc
convertOpenAcc env@(EnvPack _ _ mp) ae =
  let typeEnv  = M.map P.fst mp
      getAVr v = let (_,sa) = mp # v in expectAVar sa
  in
  case ae of
    S.Vr vr      -> getAVr vr
    S.Use accarr -> useD accarr
    S.Unit ex ->
      let ex' = convertOpenExp env ex
          ty  = S.recoverExpType (M.map P.fst mp) ex
      in unitD (scalarTypeD ty) ex'

    S.Generate initE (S.Lam1 (vr,ty) bod) ->
      let indexTy = tupTyToIndex ty -- "ty" is a plain tuple.
          bodfn ex  = let env' = extendE vr ty (indexToTup ty ex) env in
                      dbgtrace ("Generate/bodyfun called: extended environment to: "++show env')$
                      convertOpenExp env' bod
          bodty     = S.recoverExpType (M.insert vr ty typeEnv) bod
          -- TODO: Replace this by simply passing in the result type to convertAcc:
          dims = shapeTyLen$ S.recoverExpType typeEnv initE
          outArrTy  = TArray dims bodty
          init' = tupToIndex ty$ convertOpenExp env initE
      in
       dbgtrace ("Generate: computed body type: "++show bodty) $
       generateD init' bodfn outArrTy

    S.Map (S.Lam1 (vr,ty) bod) inA ->
      let bodfn ex    = convertOpenExp (extendE vr ty ex env) bod
          bodty       = S.recoverExpType (M.insert vr ty $ M.map P.fst mp) bod
      in mapD bodfn (getAVr inA) bodty

    S.ZipWith (S.Lam2 (vr1,ty1) (vr2,ty2) bod) inA inB ->
      let bodfn e1 e2 = let env' = extendE vr2 ty2 e2 $
                                   extendE vr1 ty1 e1 env
                        in convertOpenExp env' bod
          aty1@(TArray dims1 _) = P.fst (mp # inA)
          aty2@(TArray dims2 _) = P.fst (mp # inB)
          mp' = M.insert vr2 ty2 $
                M.insert vr1 ty1 typeEnv
          bodty = S.recoverExpType mp' bod
      in
      assert (dims1 == dims2) $
      zipWithD bodfn (getAVr inA) (getAVr inB) aty1 aty2 bodty

    S.Fold (S.Lam2 (v1,ty) (v2,ty2) bod) initE inA ->
      dbgtrace ("FOLD CASE.. fold of "++show (mp # inA))$
       let init' = convertOpenExp env initE
           bodfn x y = convertOpenExp (extendE v1 ty x$ extendE v2 ty y env) bod
           aty@(TArray _ inty) = P.fst (mp # inA)
           sealedInArr = getAVr inA
       in
        if ty /= ty2 || ty2 /= inty
        then error "Mal-formed Fold.  Input types to Lam2 must match eachother and array input."
        else foldD bodfn init' sealedInArr aty

    S.Replicate slc inE inA ->
      replicateD (sliceTypeD slc) (convertOpenExp env inE) (getAVr inA)


    _ -> error$"FINISHME/DynamicAcc: convertOpenAcc: unhandled array operation: " ++show ae

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
  show UnitTuple = "()"
  show (SingleTuple st) = show st
  show (PairTuple a b)  = "("++show a++","++show b++")"
  show (ThreeTuple a b c)  = "("++show a++","++show b++","++show c++")"

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
