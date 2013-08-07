{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | A library for the runtime construction of fully typed Accelerate programs.

module Data.Array.Accelerate.DynamicAcc
{-
       (-- * Dynamically typed AST pieces
         SealedExp, SealedAcc,
         
         -- * Runtime representation of Types and Constants:
         Type(..), Const(..),

         -- * Syntax-constructing functions
         constantD, useD, 
         unitD, mapD, 

         -- * Functions to convert `SimpleAcc` programs into fully-typed Accelerate
         --   programs.
         convertExp, convertClosedExp,

         t0, t1, t2  -- TEMP
       )
-}
       where

import           Data.Array.Accelerate as A 
import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Type as T
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                 (Type(..), Const(..), AVar, Var, Prog(..))
import           Data.Array.Accelerate.BackendKit.Tests (allProgsMap, p1a, TestEntry(..))
import           Data.Array.Accelerate.BackendKit.SimpleArray (payloadsFromList1)
-- import Data.Array.Accelerate.Interpreter as I
-- import           Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone (repackAcc)
import           Data.Array.Accelerate.BackendKit.Phase1.ToAccClone (repackAcc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.Array.Data  as Dat

import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone as Cvt (accToAccClone, expToExpClone)

import Data.Typeable (gcast)
import Data.Dynamic (Dynamic, fromDyn, fromDynamic, toDyn,
                     Typeable, Typeable3, mkTyConApp, TyCon, mkTyCon3, typeOf3, typeOf)
import Data.Map as M
import Prelude as P
import Data.Maybe (fromMaybe, fromJust)
-- import Data.Word
import Debug.Trace (trace)
-- import Control.Exception (bracket)
-- import Control.Monad (when)

--------------------------------------------------------------------------------
-- AST Representations
--------------------------------------------------------------------------------

-- TODO: make these pairs that keep around some printed rep for debugging purposes in
-- the case of a downcast error.  Also make them newtypes!
newtype SealedExp     = SealedExp     Dynamic deriving Show
newtype SealedOpenExp = SealedOpenExp Dynamic deriving Show
type SealedAcc = Dynamic

sealExp :: Typeable a => A.Exp a -> SealedExp
sealExp = SealedExp . toDyn

sealAcc :: Typeable a => Acc a -> SealedAcc
sealAcc = toDyn

downcastE :: forall a . Typeable a => SealedExp -> A.Exp a
downcastE (SealedExp d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
      error$"Attempt to unpack SealedExp with type "++show d
         ++ ", expected type Exp "++ show (toDyn (unused::a))

downcastA :: forall a . Typeable a => SealedAcc -> Acc a
downcastA d = case fromDynamic d of
                Just e -> e
                Nothing ->
                  error$"Attempt to unpack SealedAcc with type "++show d
                     ++ ", expected type Acc "++ show (toDyn (unused::a))

-- | Convert a `SimpleAcc` constant into a fully-typed (but sealed) Accelerate one.
constantE :: Const -> SealedExp
constantE c =
  case c of
    I   i -> sealExp$ A.constant i
    I8  i -> sealExp$ A.constant i
    I16 i -> sealExp$ A.constant i
    I32 i -> sealExp$ A.constant i
    I64 i -> sealExp$ A.constant i
    W   i -> sealExp$ A.constant i
    W8  i -> sealExp$ A.constant i
    W16 i -> sealExp$ A.constant i
    W32 i -> sealExp$ A.constant i
    W64 i -> sealExp$ A.constant i
    B   b -> sealExp$ A.constant b

--------------------------------------------------------------------------------
-- Type representations
--------------------------------------------------------------------------------                

-- | We enhance "Data.Array.Accelerate.Type.TupleType" with Elt constraints.
data EltTuple a where
  UnitTuple   ::                                               EltTuple ()
  SingleTuple :: Elt a          => T.ScalarType a           -> EltTuple a
  PairTuple   :: (Elt a, Elt b) => EltTuple a -> EltTuple b -> EltTuple (a, b)
 deriving Typeable

-- | This GADT allows monomorphic value to carry a type inside.
data SealedEltTuple where
  SealedEltTuple :: (Typeable a) =>
                    EltTuple a -> SealedEltTuple

-- | This is a bottle in which to store a type that satisfyies the Array class.
data SealedArrayType where
  -- Do we care about the ArrayElt class here?
  SealedArrayType :: Arrays a => Phantom a -> SealedArrayType

-- | Tuples of arrays rather than scalar `Elt`s.
data ArrTuple a where
  UnitTupleA   ::                                                     ArrTuple ()
  SingleTupleA :: Arrays a             => T.ScalarType a           -> ArrTuple a
  PairTupleA   :: (Arrays a, Arrays b) => ArrTuple a -> ArrTuple b -> ArrTuple (a, b)

-- TODO: CAN WE PHASE OUT SealedArrayType in favor of SealedArrTuple?
data SealedArrTuple where
  SealedArrTuple :: ArrTuple a -> SealedArrTuple

-- | Accelerate shape types, sealed up.
data SealedShapeType where
  -- Do we care about the ArrayElt class here?
  SealedShapeType :: Shape sh => Phantom sh -> SealedShapeType

-- | Just a simple signal that the value is not used, only the type.
data Phantom a = Phantom a deriving Show

-- | Dependent types!  Dynamically construct a type in a bottle.  It can be opened up
-- and used as a goal type when repacking array data or returning an Acc computation.
arrayTypeD :: Type -> SealedArrayType
arrayTypeD (TArray ndim elty) =
  case shapeTypeD ndim of
    SealedShapeType (_ :: Phantom sh) ->
     case elty of
       TInt   -> SealedArrayType (Phantom(unused:: Array sh Int))
       TFloat -> SealedArrayType (Phantom(unused:: Array sh Float))
arrayTypeD oth = error$"arrayTypeD: expected array type, got "++show oth

-- | Construct a Haskell type from an Int!  Why not?
shapeTypeD :: Int -> SealedShapeType
shapeTypeD 0 = SealedShapeType (Phantom Z)
shapeTypeD n =
  case shapeTypeD (n-1) of
    SealedShapeType (Phantom x :: Phantom sh) ->
      SealedShapeType (Phantom (x :. (unused::Int)))

-- | Convert the runtime, monomorphic type representation into a sealed container
-- with the true Haskell type inside.
scalarTypeD :: Type -> SealedEltTuple
scalarTypeD ty =
  case ty of
    TInt    -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int)
    TInt8   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int8)
    TInt16  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int16)
    TInt32  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int32)
    TInt64  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int64)

    TWord   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word)
    TArray {} -> error$"scalarTypeD: expected scalar type, got "++show ty

data SealedFun -- ??


--------------------------------------------------------------------------------
-- AST Construction
--------------------------------------------------------------------------------


-- | Dynamically typed variant of `Data.Array.Accelerate.unit`.
unitD :: SealedEltTuple -> SealedExp -> SealedAcc
unitD elt exp =
  case elt of
    SealedEltTuple (t :: EltTuple et) ->
      case t of
        UnitTuple -> sealAcc$ unit$ constant ()
        SingleTuple (_ :: T.ScalarType s) ->
          sealAcc$ unit (downcastE exp :: A.Exp  s)
        PairTuple (_ :: EltTuple l) (_ :: EltTuple r) ->
          sealAcc$ unit (downcastE exp :: A.Exp  (l,r))

-- | Dynamically-typed variant of `Data.Array.Accelerate.use`.  However, this version
-- is less powerful, it only takes a single, logical array, not a tuple of arrays.
useD :: S.AccArray -> SealedAcc
useD arr =
  case sty of
    SealedArrayType (Phantom (_ :: aT)) ->
      sealAcc$ A.use$
      repackAcc (unused::Acc aT) [arr]
 where
   dty = S.accArrayToType arr
   sty = arrayTypeD dty

-- TODO: How to handle functions?
mapD :: SealedFun -> SealedAcc -> SealedAcc 
mapD = error "mapD"


--------------------------------------------------------------------------------
-- TODO: These conversion functions could move to their own module:
--------------------------------------------------------------------------------

-- | Track the scalar, array environment, and combined, fast-access environment.
data EnvPack = EnvPack [(Var,Type)] [(AVar,Type)]
                 (M.Map Var (Type, Either SealedExp SealedAcc))


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


-- | Convert an entire `SimpleAcc` expression into a fully-typed (but sealed) Accelerate one.
--   Requires a type environments for the (open) `SimpleAcc` expression:    
--   one for free expression variables, one for free array variables.
--     
convertExp :: 
              EnvPack -> S.Exp -> SealedExp
convertExp ep@(EnvPack envE envA mp)
--           slayout@(SealedLayout (lyt :: Layout env0 env0'))
           ex =
--  trace("Converting exp "++show ex++" with layout "++show lyt++" and dyn env "++show (envE,envA))$
  let cE = convertExp ep in 
  case ex of
    S.EConst c -> constantE c

    -- This is tricky, because it needs to become a deBruin index ultimately...
    -- Or we need to stay at the level of HOAS...
    S.EVr vr -> case mp # vr of (_,Left se) -> se 

    S.ELet (vr,ty,rhs) bod ->
      let rhs' = cE rhs
          ep'@(EnvPack _ _ m2) = extendE vr ty rhs' ep
          resTy = scalarTypeD (S.recoverExpType (M.map P.fst m2) bod)
          sty   = scalarTypeD ty
      in
       convertExp ep' bod

    S.ECond e1 e2 e3 ->
      let d1 = cE e1
          d2 = cE e2
          d3 = cE e3
          ty = S.recoverExpType (M.map P.fst mp) e2
      in case scalarTypeD ty of
          SealedEltTuple (t :: EltTuple elt) ->
           -- #define a macro for this?
           case t of
             UnitTuple -> 
               sealExp(((downcastE d1::Exp Bool) A.?
                        (downcastE d2::Exp elt,
                         downcastE d3::Exp elt))::Exp elt)
             SingleTuple _ ->
               sealExp(((downcastE d1::Exp Bool) A.?
                        (downcastE d2::Exp elt,
                         downcastE d3::Exp elt))::Exp elt)
             PairTuple _ _ ->
               sealExp(((downcastE d1::Exp Bool) A.?
                        (downcastE d2::Exp elt,
                         downcastE d3::Exp elt))::Exp elt)


-- | Convert a closed `SimpleAcc` expression (no free vars) into a fully-typed (but
-- sealed) Accelerate one.
convertClosedExp :: S.Exp -> SealedExp
convertClosedExp ex = SealedExp $ 
  case ex of
    S.EVr v -> error$"convertClosedExp: free variable found: "++show v

convertProg :: S.Prog a -> SealedAcc
convertProg S.Prog{progBinds,progResults} =
  error "convertProg"


--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------    

instance Show (EltTuple a) where
  show UnitTuple = "()"
  show (SingleTuple st) = show st
  show (PairTuple a b)  = "("++show a++","++show b++")"

instance Show SealedEltTuple where
  show (SealedEltTuple x) = "Sealed:"++show x

instance Show SealedShapeType where
  show (SealedShapeType (Phantom (_ :: sh))) =
    "Sealed:"++show (toDyn (unused::sh))
    
instance Show SealedArrayType where
  show (SealedArrayType (Phantom (_ :: sh))) =
    "Sealed:"++show (toDyn (unused::sh))


--------------------------------------------------------------------------------
-- Misc, Tests, and Examples
--------------------------------------------------------------------------------  

unused :: a
unused = error "This dummy value should not be used"

-- | For debugging purposes we should really never use Data.Map.!  This is an
-- alternative with a better error message.
(#) :: (Ord a1, Show a, Show a1) => M.Map a1 a -> a1 -> a
mp # k = case M.lookup k mp of
          Nothing -> error$"Map.lookup: key "++show k++" is not in map:\n  "++show mp
          Just x  -> x

c0 :: SealedExp
c0 = constantE (I 99)

c0a :: A.Exp Int
c0a = downcastE c0

{-
-- Small tests:
t0 :: SealedAcc
t0 = convertClosedAExp $
     S.Use (S.AccArray [5,2] (payloadsFromList1$ P.map I [1..10]))
t0b :: Acc (Array DIM2 (Int))
t0b = downcastA t0
-}

t1 = -- convertClosedExp
     convertExp emptyEnvPack 
     (S.ECond (S.EConst (B True)) (S.EConst (I 33)) (S.EConst (I 34)))
t1a :: A.Exp Int
t1a = downcastE t1

t2 :: SealedExp
t2 = convertExp emptyEnvPack 
     (S.ELet (v, TInt, (S.EConst (I 33))) (S.EVr v))
 where v = S.var "v" 

t2a :: Exp Int
t2a = downcastE t2

t4 = simpleProg
 where
   TestEntry {simpleProg} = allProgsMap # "p1a"

