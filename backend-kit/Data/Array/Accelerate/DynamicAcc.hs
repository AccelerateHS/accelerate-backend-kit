{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs #-}

-- | A library for the runtime construction of fully typed Accelerate programs.

module Data.Array.Accelerate.DynamicAcc
       (-- * Dynamically typed AST pieces
         SealedExp, SealedAcc,
         
         -- * Runtime representation of Types and Constants:
         Type(..), Const(..),

         -- * Syntax-constructing functions
         constantD, useD, 
         unitD, mapD, 

         -- * Functions to convert `SimpleAcc` programs into fully-typed Accelerate
         --   programs.
         convertExp, convertClosedExp
       )
       where

import           Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Type as T
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                 (Type(..), Const(..), Var)

-- import Data.Array.Accelerate.Interpreter as I
-- import qualified Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone as C
-- import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.Array.Data  as Dat

import Data.Typeable
import Data.Dynamic
import Data.Map as M
import Prelude as P
-- import Data.Maybe
-- import Data.Word
-- import Debug.Trace
-- import Control.Exception (bracket)
-- import Control.Monad (when)

--------------------------------------------------------------------------------

-- TODO: make these pairs that keep around some printed rep for debugging purposes:
type SealedExp = Dynamic
type SealedAcc = Dynamic

sealExp :: Typeable a => Exp a -> SealedExp
sealExp = toDyn

sealAcc :: Typeable a => Acc a -> SealedAcc
sealAcc = toDyn

downcastE :: forall a . Typeable a => SealedExp -> Exp a
downcastE d = case fromDynamic d of
                Just e -> e
                Nothing ->
                  error$"Attempt to unpack SealedExp with type "++show d
                     ++ ", expected type "++ show (toDyn (unused::a))

downcastA :: forall a . Typeable a => SealedAcc -> Acc a
downcastA d = case fromDynamic d of
                Just e -> e
                Nothing ->
                  error$"Attempt to unpack SealedAcc with type "++show d
                     ++ ", expected type "++ show (toDyn (unused::a))

-- | We enhance "Data.Array.Accelerate.Type.TupleType" with Elt constraints.
data EltTuple a where
  UnitTuple   ::                                               EltTuple ()
  SingleTuple :: Elt a          => T.ScalarType a           -> EltTuple a
  PairTuple   :: (Elt a, Elt b) => EltTuple a -> EltTuple b -> EltTuple (a, b)

-- | This GADT allows monomorphic value to carry a type inside.
data SealedEltTuple where
  SealedEltTuple :: EltTuple a -> SealedEltTuple

data SealedFun -- ??

-- | This is a bottle in which to store a type that satisfyies the Array class.
data SealedArrayType where
  -- Do we care about the ArrayElt class here?
  SealedArrayType :: Arrays a => Phantom a -> SealedArrayType

data SealedShapeType where
  -- Do we care about the ArrayElt class here?
  SealedShapeType :: Shape sh => Phantom sh -> SealedShapeType

-- | Just a simple signal that the value is not used, only the type.
data Phantom a = Phantom a

--------------------------------------------------------------------------------

-- | Dynamically typed variant of `Data.Array.Accelerate.unit`.
unitD :: SealedEltTuple -> SealedExp -> SealedAcc
unitD elt exp =
  case elt of
    SealedEltTuple (t :: EltTuple et) ->
      case t of
        UnitTuple -> toDyn$ unit$ constant ()
        SingleTuple (st :: T.ScalarType s) ->
          toDyn$ unit (downcastE exp :: Exp s)
        PairTuple (_ :: EltTuple l) (_ :: EltTuple r) ->
          toDyn$ unit (downcastE exp :: Exp (l,r))

useD :: S.AccArray -> SealedAcc
useD = undefined
  -- We have that repackAcc function for this perhaps... IF we know what type we want
  -- to go to.  But at this point we don't really.       
       

-- TODO: How to handle functions?
mapD :: SealedFun -> SealedAcc -> SealedAcc 
mapD = undefined

-- | Convert a `SimpleAcc` constant into a fully-typed (but sealed) Accelerate one.
constantD :: Const -> SealedExp
constantD c =
  case c of
    I  i -> sealExp$ A.constant i
    I8 i -> sealExp$ A.constant i

-- | Dependent types!  Dynamically construct a type in a bottle.  It can be opened up
-- and used as a goal type when repacking array data or returning an Acc computation.
arrayTypeD :: Type -> SealedArrayType
arrayTypeD (TArray ndim elty) =
  case shapeTypeD ndim of
    SealedShapeType (_ :: Phantom sh) ->
     case elty of
       TInt   -> SealedArrayType (Phantom(unused:: Array sh Int))
       TFloat -> SealedArrayType (Phantom(unused:: Array sh Float))

-- | Construct a Haskell type from an Int!
shapeTypeD :: Int -> SealedShapeType
shapeTypeD 0 = SealedShapeType (Phantom Z)
shapeTypeD n =
  case shapeTypeD (n-1) of
    SealedShapeType (x :: Phantom sh) ->
      undefined
      -- SealedShapeType (Phantom (x :. ()))


--------------------------------------------------------------------------------
-- TODO: These conversion functions could move to their own module:

-- convertExp :: S.Exp -> (forall a . Elt a => Exp a)
-- | Convert an entire `SimpleAcc` expression into a fully-typed (but sealed) Accelerate one.
--   Requires a type environment for the (open) `SimpleAcc` expression.
convertExp :: M.Map Var Type -> S.Exp -> SealedExp
convertExp env ex =
  case ex of
    S.EConst c -> constantD c
    -- This is tricky, because it needs to become a deBruin index ultimately...
    -- Or we need to stay at the level of HOAS...
--     S.EVr v    -> env#v

-- | Convert a closed `SimpleAcc` expression (no free vars) into a fully-typed (but
-- sealed) Accelerate one.
convertClosedExp :: S.Exp -> SealedExp
convertClosedExp ex =
  case ex of
    S.EVr v -> error$"convertClosedExp: free variable found: "++show v


--------------------------------------------------------------------------------
-- Misc

unused :: a
unused = error "This dummy value should not be used"

-- | For debugging purposes we should really never use Data.Map.!  This is an
-- alternative with a better error message.
(#) :: (Ord a1, Show a, Show a1) => M.Map a1 a -> a1 -> a
mp # k = case M.lookup k mp of
          Nothing -> error$"Map.lookup: key "++show k++" is not in map:\n  "++show mp
          Just x  -> x
