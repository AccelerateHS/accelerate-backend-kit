
-- | PHASE1 :  Accelerate -> SimpleAcc
--
-- This module provides a function to convert from Accelerate's
-- internal representation to the `SimpleAcc` external representation.
-- This representation retains nearly the full set of Accelerate
-- language constructs.  Desugaring is postponed to phase 2.
module Data.Array.Accelerate.BackendKit.CompilerPipeline
       (
         -- * Major compiler phases:
         phase1, phase2, phase3,
         -- * Reexport from ToAccClone:
         unpackArray, packArray, repackAcc, Phantom,
         -- * Internal bits, exported for now:
         phase2A         
       )
       where

import qualified Data.Array.Accelerate.Smart       as Sug
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike     as C
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
import           Data.Array.Accelerate.BackendKit.IRs.Metadata   (ArraySizeEstimate, FreeVars)
import           Data.Array.Accelerate.BackendKit.CompilerUtils  (runPass, runOptPass)

-- Phase 1 passes:
----------------------------------------
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone        (accToAccClone,unpackArray, packArray, repackAcc, Phantom)
import Data.Array.Accelerate.BackendKit.Phase1.LiftLets          (gatherLets)
import Data.Array.Accelerate.BackendKit.Phase1.LiftComplexRands  (liftComplexRands)
import Data.Array.Accelerate.BackendKit.Phase1.RemoveArrayTuple  (removeArrayTuple)
import Data.Array.Accelerate.BackendKit.Phase1.StaticTuples      (staticTuples)

-- Phase 2 passes:
----------------------------------------
import Data.Array.Accelerate.BackendKit.Phase2.DesugarUnit       (desugarUnit)
import Data.Array.Accelerate.BackendKit.Phase2.SizeAnalysis      (sizeAnalysis)
import Data.Array.Accelerate.BackendKit.Phase2.ExplicitShapes    (explicitShapes)
import Data.Array.Accelerate.BackendKit.Phase2.TrackUses         (trackUses)
import Data.Array.Accelerate.BackendKit.Phase2.FuseMaps          (fuseMaps)
import Data.Array.Accelerate.BackendKit.Phase2.DesugToBackperm   (desugToBackperm)
import Data.Array.Accelerate.BackendKit.Phase2.DesugToGenerate   (desugToGenerate)
import Data.Array.Accelerate.BackendKit.Phase2.EstimateCost      (estimateCost)
import Data.Array.Accelerate.BackendKit.Phase2.InlineCheap       (inlineCheap)
import Data.Array.Accelerate.BackendKit.Phase2.DeadArrays        (deadArrays)
import Data.Array.Accelerate.BackendKit.Phase2.OneDimensionalize (oneDimensionalize)
import Data.Array.Accelerate.BackendKit.Phase2.NormalizeExps     (normalizeExps)
import Data.Array.Accelerate.BackendKit.Phase2.UnzipETups        (unzipETups)
import Data.Array.Accelerate.BackendKit.Phase2.ToCLike           (convertToCLike)

-- Phase 3 passes:
----------------------------------------
import Data.Array.Accelerate.BackendKit.Phase3.KernFreeVars      (kernFreeVars)
import Data.Array.Accelerate.BackendKit.Phase3.ToGPUIR           (convertToGPUIR)
import Data.Array.Accelerate.BackendKit.Phase3.DesugarGenerate   (desugarGenerate)
import Data.Array.Accelerate.BackendKit.Phase3.DesugarFoldScan   (desugarFoldScan)

--------------------------------------------------------------------------------
-- Exposed entrypoints for this module:
--------------------------------------------------------------------------------

-- | The final step: Lower to a GPU-targetting language.
phase3 :: C.LLProg () -> G.GPUProg (FreeVars)
phase3 prog = 
  runPass    "desugarGenerate"   desugarGenerate   $     -- (size,freevars)
  runPass    "desugarFoldScan"   desugarFoldScan   $     -- (size,freevars)
  runPass    "convertToGPUIR"    convertToGPUIR    $     -- (size,freevars)
  runPass    "kernFreeVars"      kernFreeVars      $     -- (freevars)
  prog
  
-- | The bulk of the compilation process -- eliminate unnecessary
-- forms and lower the language.
phase2 :: S.Prog () -> C.LLProg ()
phase2 prog =
  runPass    "convertToCLike"    convertToCLike    $     -- ()
  runPass    "typecheck3"        typecheckPass     $     -- (size)
  runPass    "unzipETups"        unzipETups        $     -- (size)  
  runPass    "normalizeExps"     normalizeExps     $     -- (size)
  phase2A    prog

-- | Factor out this [internal] piece for use in some place(s).
phase2A :: S.Prog () -> S.Prog ArraySizeEstimate
phase2A prog =
  runPass    "typecheck2"        typecheckPass     $       
  runPass    "oneDimensionalize" oneDimensionalize $     -- (size)
  runOptPass "deadArrays"        deadArrays (fmap fst) $ -- (size)
  runPass    "trackUses"         trackUses         $     -- (size,uses)
   -- NOTE INLINE CHEAP IS NOT OPTIONAL PRESENTLY! (needed for copy-prop)
--   runOptPass "inlineCheap"       inlineCheap (fmap fst) $ -- (size)
  runPass    "inlineCheap"       inlineCheap       $      -- (size)
  runPass    "estimateCost"      estimateCost      $      -- (size,cost)
  runPass    "desugtoGenerate"   desugToGenerate   $      -- (size)
  runPass    "desugToBackperm"   desugToBackperm   $      -- (size,uses)
  runOptPass "fuseMaps"          fuseMaps  id      $      -- (size,uses)
  runPass    "trackUses"         trackUses         $      -- (size,uses)
  runPass    "explicitShapes"    explicitShapes    $      -- (size)
  runPass    "sizeAnalysis"      sizeAnalysis      $      -- (size)
  runPass    "desugarUnit"       desugarUnit       $      -- ()
  prog

-- | Convert the sophisticate Accelerate-internal AST representation
--   into something very simple for external consumption.  Note: this
--   involves applying a number of lowering compiler passes.
phase1 :: Sug.Arrays a => Sug.Acc a -> S.Prog ()
phase1 prog =
  runPass "typecheck1"           typecheckPass     $       
  runPass "removeArrayTuple"     removeArrayTuple  $ -- convert to S.Prog
  runPass "gatherLets"           gatherLets        $  
  runPass "liftComplexRands"     liftComplexRands  $  
  runPass "staticTuples"         staticTuples      $
  runPass "initialConversion"    accToAccClone     $ 
  prog

typecheckPass :: S.Prog a -> S.Prog a
typecheckPass prog =
  case S.typecheckProg prog of
    Nothing -> prog
    Just s -> error$"Typecheck pass failed: "++s
