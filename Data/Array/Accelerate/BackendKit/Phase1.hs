{-# LANGUAGE BangPatterns, GADTs, ScopedTypeVariables, CPP, TupleSections, PatternGuards #-}

{-# OPTIONS_GHC -fwarn-unused-imports #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- {-# ANN module "HLint: ignore Eta reduce" #-}

-- TODO LIST:
--   * Audit treatment of shapes and indices
--   * Audit tuple flattening guarantees
--   * Add type info to some language forms... 
--   * Convert boundary

-- Toggle this to try to match the source tuple format rather than the
-- Snoc-list accelerate internal format.
#define SURFACE_TUPLES

-- | PHASE1 :  Accelerate -> SimpleAcc
--
-- This module provides a function to convert from Accelerate's
-- internal representation to the `SimpleAcc` external representation.
-- This representation retains nearly the full set of Accelerate
-- language constructs.  Desugaring is postponed to phase 2.
module Data.Array.Accelerate.BackendKit.Phase1
       ( convertToSimpleProg )
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
import           Data.Array.Accelerate.AST
import           Data.Array.Accelerate.Tuple
import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.Trafo.Sharing as Cvt
import qualified Data.Array.Accelerate.BackendKit.SimpleArray as SA
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
  -- Temporary AST before we get to the final one:
import qualified Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone as T

-- Lowering passes:
import           Data.Array.Accelerate.BackendKit.Passes.LiftLets         (gatherLets)
import           Data.Array.Accelerate.BackendKit.Passes.LiftComplexRands (liftComplexRands)
import           Data.Array.Accelerate.BackendKit.Passes.RemoveArrayTuple (removeArrayTuple)
import           Data.Array.Accelerate.BackendKit.Passes.StaticTuples     (staticTuples)
import           Data.Array.Accelerate.BackendKit.CompilerUtils (runPass)

import           Data.Array.Accelerate.BackendKit.Passes.ToAccClone (accToAccClone)

--------------------------------------------------------------------------------
-- Exposed entrypoints for this module:
--------------------------------------------------------------------------------

-- | Convert the sophisticate Accelerate-internal AST representation
--   into something very simple for external consumption.  Note: this
--   involves applying a number of lowering compiler passes.
convertToSimpleProg :: Sug.Arrays a => Sug.Acc a -> S.Prog ()
convertToSimpleProg prog = 
  runPass "removeArrayTuple" removeArrayTuple $     
  runPass "gatherLets"       gatherLets $  
  runPass "liftComplexRands" liftComplexRands $  
  
  runPass "staticTuples"     staticTuples     $   
  runPass "initialConversion"  accToAccClone  $ 
  prog

