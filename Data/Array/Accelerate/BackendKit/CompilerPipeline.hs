
-- | PHASE1 :  Accelerate -> SimpleAcc
--
-- This module provides a function to convert from Accelerate's
-- internal representation to the `SimpleAcc` external representation.
-- This representation retains nearly the full set of Accelerate
-- language constructs.  Desugaring is postponed to phase 2.
module Data.Array.Accelerate.BackendKit.CompilerPipeline
       ( convertToSimpleProg,
         -- Reexport from ToAccClone:
         unpackArray, packArray, repackAcc, Phantom
       )
       where

import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.CompilerUtils           (runPass)

-- Phase 1 passes:
----------------------------------------
import           Data.Array.Accelerate.BackendKit.Phase1.ToAccClone 
import           Data.Array.Accelerate.BackendKit.Phase1.LiftLets         (gatherLets)
import           Data.Array.Accelerate.BackendKit.Phase1.LiftComplexRands (liftComplexRands)
import           Data.Array.Accelerate.BackendKit.Phase1.RemoveArrayTuple (removeArrayTuple)
import           Data.Array.Accelerate.BackendKit.Phase1.StaticTuples     (staticTuples)

-- Phase 2 passes:
----------------------------------------

import Data.Array.Accelerate.BackendKit.Phase2.DesugarUnit (desugarUnit)

-- import B629.SizeAnalysis      (sizeAnalysis)
-- import B629.TrackUses         (trackUses)
-- import B629.FuseMaps          (fuseMaps)
-- import B629.EmitOpenCL        (emitOpenCL)
-- import B629.EmitC             (emitC)
-- import B629.DeadArrays        (deadArrays)
-- import B629.InlineCheap       (inlineCheap)
-- import B629.DesugToBackperm   (desugToBackperm)
-- import B629.DesugToGenerate   (desugToGenerate)
-- import B629.EstimateCost      (estimateCost)
-- import B629.KernFreeVars      (kernFreeVars)
-- import B629.ExplicitShapes    (explicitShapes)
-- import B629.UnzipETups        (unzipETups)
-- import B629.NormalizeExps     (normalizeExps)
-- import B629.ConvertLLIR       (convertLLIR)
-- import B629.OneDimensionalize (oneDimensionalize)
-- import B629.ConvertGPUIR      (convertGPUIR)
-- import B629.LowerGPUIR        (lowerGPUIR)




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


