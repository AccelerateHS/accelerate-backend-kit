{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs #-}

-- | A library for the runtime construction of fully typed Accelerate programs.

module Data.Array.Accelerate.DynamicAcc
       (-- * Dynamically typed AST pieces
         SealedExp, SealedAcc,
         
         -- * Runtime representation of Types
         Type(..),

         -- * Syntax-constructing functions
         unitD

         -- * Functions to convert `SimpleAcc` programs into fully-typed Accelerate
         --   programs.
       )
       where

import Prelude as P
import Data.Array.Accelerate as A
-- import Data.Array.Accelerate.Interpreter as I
-- import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..))
-- import qualified Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone as C
-- import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.Array.Data  as Dat
import qualified Data.Array.Accelerate.Type as T

-- import Data.Maybe
import Data.Typeable
import Data.Dynamic
-- import Data.Word
-- import Debug.Trace
-- import Control.Exception (bracket)
-- import Control.Monad (when)

--------------------------------------------------------------------------------

-- TODO: make these pairs that keep around some printed rep for debugging purposes:
type SealedExp = Dynamic
type SealedAcc = Dynamic

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



--------------------------------------------------------------------------------
-- Misc

unused :: a
unused = error "This dummy value should not be used"
