
-- | PHASE1 :  Accelerate -> SimpleAcc
--
-- This module provides a function to convert from Accelerate's
-- internal representation to the `SimpleAcc` external representation.
-- This representation retains nearly the full set of Accelerate
-- language constructs.  Desugaring is postponed to phase 2.
module Data.Array.Accelerate.BackendKit.Phase1
       ( convertToSimpleProg,
         -- Reexport from ToAccClone:
         unpackArray, packArray, repackAcc, Phantom
       )
       where

import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
--               Lowering passes:
import           Data.Array.Accelerate.BackendKit.Passes.LiftLets         (gatherLets)
import           Data.Array.Accelerate.BackendKit.Passes.LiftComplexRands (liftComplexRands)
import           Data.Array.Accelerate.BackendKit.Passes.RemoveArrayTuple (removeArrayTuple)
import           Data.Array.Accelerate.BackendKit.Passes.StaticTuples     (staticTuples)
import           Data.Array.Accelerate.BackendKit.CompilerUtils           (runPass)

import           Data.Array.Accelerate.BackendKit.Passes.ToAccClone 

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

