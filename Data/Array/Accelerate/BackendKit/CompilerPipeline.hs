
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

import Data.Array.Accelerate.BackendKit.Phase2.DesugarUnit       (desugarUnit)
import Data.Array.Accelerate.BackendKit.Phase2.SizeAnalysis      (sizeAnalysis)
--- import Data.Array.Accelerate.BackendKit.Phase2.TrackUses         (trackUses)
-- import Data.Array.Accelerate.BackendKit.Phase2.FuseMaps          (fuseMaps)
-- import Data.Array.Accelerate.BackendKit.Phase2.EmitOpenCL        (emitOpenCL)
-- import Data.Array.Accelerate.BackendKit.Phase2.EmitC             (emitC)
-- import Data.Array.Accelerate.BackendKit.Phase2.DeadArrays        (deadArrays)
-- import Data.Array.Accelerate.BackendKit.Phase2.InlineCheap       (inlineCheap)
-- import Data.Array.Accelerate.BackendKit.Phase2.DesugToBackperm   (desugToBackperm)
-- import Data.Array.Accelerate.BackendKit.Phase2.DesugToGenerate   (desugToGenerate)
-- import Data.Array.Accelerate.BackendKit.Phase2.EstimateCost      (estimateCost)
-- import Data.Array.Accelerate.BackendKit.Phase2.KernFreeVars      (kernFreeVars)
-- import Data.Array.Accelerate.BackendKit.Phase2.ExplicitShapes    (explicitShapes)
-- import Data.Array.Accelerate.BackendKit.Phase2.UnzipETups        (unzipETups)
-- import Data.Array.Accelerate.BackendKit.Phase2.NormalizeExps     (normalizeExps)
-- import Data.Array.Accelerate.BackendKit.Phase2.ConvertLLIR       (convertLLIR)
-- import Data.Array.Accelerate.BackendKit.Phase2.OneDimensionalize (oneDimensionalize)
-- import Data.Array.Accelerate.BackendKit.Phase2.ConvertGPUIR      (convertGPUIR)
-- import Data.Array.Accelerate.BackendKit.Phase2.LowerGPUIR        (lowerGPUIR)




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


-- b629Compiler :: S.Prog () -> G.GPUProg ()
-- b629Compiler prog =
--   runPass    "lowerGPUIR"        lowerGPUIR        $     -- ()
--   runPass    "convertGPUIR"      convertGPUIR      $     -- ()
--   runPass    "kernFreeVars"      kernFreeVars      $     -- (size,freevars)
--   runPass    "convertLLIR"       convertLLIR       $     -- (size)
--   runPass    "unzipETups"        unzipETups        $     -- (size)  
--   runPass    "normalizeExps"     normalizeExps     $     -- (size)
--   runPass    "oneDimensionalize" oneDimensionalize $     -- (size)
--   runOptPass "deadArrays"        deadArrays (fmap fst) $ -- (size)
--   runPass    "trackUses"         trackUses         $     -- (size,uses)
--    -- NOTE INLINE CHEAP IS NOT OPTIONAL PRESENTLY! (needed for copy-prop)
-- --   runOptPass "inlineCheap"       inlineCheap (fmap fst) $ -- (size)
--   runPass    "inlineCheap"       inlineCheap       $      -- (size)
--   runPass    "estimateCost"      estimateCost      $      -- (size,cost)
--   runPass    "desugtoGenerate"   desugToGenerate   $      -- (size)
--   runPass    "desugToBackperm"   desugToBackperm   $      -- (size,uses)
--   runOptPass "fuseMaps"          fuseMaps  id      $      -- (size,uses)
--   runPass    "trackUses"         trackUses         $      -- (size,uses)
--   runPass    "explicitShapes"    explicitShapes    $      -- (size)
--   runPass    "sizeAnalysis"      sizeAnalysis      $      -- (size)
--   runPass    "desugarUnit"       desugarUnit       $      -- ()
--   prog
