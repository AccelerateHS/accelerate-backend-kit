{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

module Data.Array.Accelerate.BackendKit.CompilerPipeline
       (
         -- * Major compiler phases:
         phase0, phase1, phase2, phase3, defaultTrafoConfig,
         -- * Reexport from ToAccClone:
         unpackArray, packArray, repackAcc, Phantom,

         -- * Compiler construction
         runPass, 
         runSAPass1D, runSAPassND, runSAPassNoD,
         runOptPass, runOptPassNoD, runOptPassND,
         
         -- * Internal bits, exported for now:
         phase2A, typecheckPass, optionalTC, DimCheckMode(..)
       )
       where

import           Text.PrettyPrint.GenericPretty (Out(..))
import           Text.PrettyPrint.HughesPJ (text)
import           Debug.Trace (trace)

import qualified Data.Array.Accelerate.AST         as AST
import qualified Data.Array.Accelerate.Smart       as Smt
import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import           Data.Array.Accelerate.Trafo.Sharing (convertAcc)
import           Data.Array.Accelerate.Trafo (convertAccWith, Phase(..))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike     as C
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
import           Data.Array.Accelerate.BackendKit.IRs.Metadata   (Stride, ArraySizeEstimate, FreeVars)
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (maybtrace, dbg)

-- Phase 1 passes:
----------------------------------------
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone        (accToAccClone,unpackArray, packArray, repackAcc, Phantom)
import Data.Array.Accelerate.BackendKit.Phase1.LiftLets          (gatherLets)
import Data.Array.Accelerate.BackendKit.Phase1.LiftComplexRands  (liftComplexRands)
import Data.Array.Accelerate.BackendKit.Phase1.StaticTuples      (staticTuples)
import Data.Array.Accelerate.BackendKit.Phase1.RemoveArrayTuple  (removeArrayTuple)
import Data.Array.Accelerate.BackendKit.Phase1.VerifySimpleAcc   (verifySimpleAcc, VerifierConfig(..), DimCheckMode(..))

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
import Data.Array.Accelerate.BackendKit.Phase2.DeadCode          (deadCode)
import Data.Array.Accelerate.BackendKit.Phase2.OneDimensionalize (oneDimensionalize)
import Data.Array.Accelerate.BackendKit.Phase2.NormalizeExps     (normalizeExps)
import Data.Array.Accelerate.BackendKit.Phase2.UnzipETups        (unzipETups)
import Data.Array.Accelerate.BackendKit.Phase2.UnzipArrays       (unzipArrays)
import Data.Array.Accelerate.BackendKit.Phase2.ToCLike           (convertToCLike)

-- Phase 3 passes:
----------------------------------------
import Data.Array.Accelerate.BackendKit.Phase3.KernFreeVars      (kernFreeVars)
import Data.Array.Accelerate.BackendKit.Phase3.ToGPUIR           (convertToGPUIR)
import Data.Array.Accelerate.BackendKit.Phase3.FuseGenReduce     (fuseGenReduce)
import Data.Array.Accelerate.BackendKit.Phase3.DesugarFoldScan   (desugarFoldScan)
import Data.Array.Accelerate.BackendKit.Phase3.DesugarGenerate   (desugarGenerate)


--------------------------------------------------------------------------------
-- The major pieces of the compiler.
--------------------------------------------------------------------------------

-- | Phase3: The final step: Lower to a GPU-targetting language.  Perform
-- optimizations that have been waiting on the alternate representation.
phase3 :: C.LLProg () -> G.GPUProg (FreeVars)
phase3 prog =
  runPass    "desugarGenerate"   desugarGenerate   $     -- (freevars)
  runPass    "desugarFoldScan"   desugarFoldScan   $     -- (freevars)
  runOptPass "fuseGenReduce"     fuseGenReduce  id $     -- (freevars)  
  runPass    "convertToGPUIR"    convertToGPUIR    $     -- (freevars)
  runPass    "kernFreeVars"      kernFreeVars      $     -- (freevars)
  prog
  
-- | Phase2: The bulk of the compilation process -- eliminate unnecessary
-- forms and lower the language.
phase2 :: S.Prog () -> C.LLProg ()
phase2 prog =
  runPass    "convertToCLike"    convertToCLike    $     -- ()  
  -- todo: Verify final CLike here
  runPass    "unzipArrays"       unzipArrays       $     -- (opinputs,(subbinds,(foldstride,size)))
  runPass    "unzipETups"        unzipETups        $     -- (subbinds,(foldstride,size))
  runSAPass1D "normalizeExps"    normalizeExps     $     -- (foldstride,size)
  phase2A    prog

-- | Factor out this [internal] piece for use in some place(s).
phase2A :: S.Prog () -> S.Prog (Maybe (Stride S.Exp),ArraySizeEstimate)
phase2A prog =
  runSAPass1D  "oneDimensionalize" oneDimensionalize   $  -- (foldstride,size)
  runOptPassNoD "deadCode"          deadCode (fmap fst) $  -- (size)
  runSAPassNoD  "trackUses"         trackUses           $  -- (size,uses)
  runOptPassNoD "inlineCheap"     inlineCheap (fmap fst) $ -- (size)
  runSAPassNoD  "estimateCost"    estimateCost      $      -- (size,cost)
  runSAPassNoD  "desugtoGenerate" desugToGenerate   $      -- (size)
  runSAPassNoD  "desugToBackperm" desugToBackperm   $      -- (size,uses)
  runOptPassNoD  "fuseMaps"       fuseMaps  id      $      -- (size,uses)
  runSAPassNoD   "trackUses"      trackUses         $      -- (size,uses)
  runSAPassNoD "explicitShapes"   explicitShapes    $      -- (size)
  runSAPassND "sizeAnalysis"     sizeAnalysis      $      -- (size)
  runSAPassND "desugarUnit"      desugarUnit       $      -- ()
  prog

-- | Phase1: Convert the sophisticate Accelerate-internal AST representation into
-- something very simple for external consumption.  Note: this involves applying a
-- number of lowering compiler passes.
phase1 :: (Sug.Arrays a) => AST.Acc a -> S.Prog ()
phase1 prog =
  optionalTC                     typecheckND       $  -- Initial Typecheck
  runPass "removeArrayTuple"     removeArrayTuple  $ -- convert to S.Prog -- does gensym! FIXME
  runPass "gatherLets"           gatherLets        $  
  runPass "liftComplexRands"     liftComplexRands  $ -- does gensym! FIXME
  runPass "staticTuples"         staticTuples      $
  runPass "initialConversion"    accToAccClone     $ -- does gensym! FIXME
  runPass "beforeConversion"     id                $ 
  prog

-- | This simply calls the Accelerate *front-end* with the default settings for a
-- backend-kit compiler.
phase0 :: Sug.Arrays a => Smt.Acc a -> AST.Acc a
-- phase0 = convertAcc True True True
phase0 = convertAccWith defaultTrafoConfig

-- NOTE: This is the same configuration as used by the CUDA backend:
--
-- How the Accelerate program should be interpreted.
-- TODO: make sharing/fusion runtime configurable via debug flags or otherwise.
--
defaultTrafoConfig :: Phase
defaultTrafoConfig =  Phase
  { recoverAccSharing      = True
  , recoverExpSharing      = True
  , floatOutAccFromExp     = True
  -- Turning this off so that we can measure the efficacy of the backend-kit fusion alone:
  -- (Also, we don't support the IR generated by the output of Trafo fusion.)
  , enableAccFusion        = False
  -- Turning this one on causes the D.A.A.Interpreter to fail three tests!
  , convertOffsetOfSegment = False
  }


--------------------------------------------------------------------------------    
-- Type Checking
--------------------------------------------------------------------------------

typecheckND :: S.Prog a -> S.Prog a
typecheckND = typecheckPass NDim

typecheck1D :: S.Prog a -> S.Prog a
typecheck1D = typecheckPass OneDim

typecheckPass :: DimCheckMode -> S.Prog a -> S.Prog a
typecheckPass dimMode prog =
  case verifySimpleAcc VerifierConfig{dimMode} prog of
    Nothing -> prog
    Just s -> error$"Typecheck pass failed: "++s

--------------------------------------------------------------------------------    
-- Compiler Construction:
--------------------------------------------------------------------------------

-- TODO: Enable profiling support and a more sophisticated runtime representation of Compilers.

-- | Pass composition:
runPass :: Out a => String -> (t -> a) -> t -> a
runPass msg pass input =
  let output = pass input in
  if dbg>=4 then
    -- (trace ("\n" ++ msg ++ ", output was:\n"++
    --        "================================================================================\n"
    --        ++show (doc output))
    --  output)

    input `seq` 
    (trace ("\n" ++ msg ++ ", output was:\n"++
           "================================================================================\n")
     (trace (show (doc output)) output))
  else output

-- An [optional] optimization pass:
runOptPass :: Out a => String -> (t -> a) -> (t -> a) -> t -> a
runOptPass str pass _otherwise =
  runPass str pass

-- An optional pass with typechecking
runOptPassND :: Out a => String -> (S.Prog t -> S.Prog a) -> (S.Prog t -> S.Prog a) -> S.Prog t -> S.Prog a
runOptPassND str pass _otherwise =
  runSAPassND str pass

runOptPassNoD :: Out a => String -> (S.Prog t -> S.Prog a) -> (S.Prog t -> S.Prog a) -> S.Prog t -> S.Prog a
runOptPassNoD str pass _otherwise =
  runSAPassNoD str pass

-- | A specific variant for passes that produce N-dimensional `SimpleAcc` output.
runSAPassND :: Out a => String -> (S.Prog t -> S.Prog a) -> S.Prog t -> S.Prog a
runSAPassND msg pass input =
  optionalTC typecheckND $ 
  runPass msg pass input

-- | This version allows implicit coercion between different dimensionalities.
-- I.e. reshape desugars to NOTHING.
runSAPassNoD :: Out a => String -> (S.Prog t -> S.Prog a) -> S.Prog t -> S.Prog a
runSAPassNoD msg pass input =
  optionalTC (typecheckPass NoDim) $  
  runPass msg pass input


-- | A specific variant for passes that produce 1-dimensional `SimpleAcc` output.
runSAPass1D :: Out a => String -> (S.Prog t -> S.Prog a) -> S.Prog t -> S.Prog a
runSAPass1D msg pass input =
  optionalTC typecheck1D $
  runPass msg pass input


optionalTC :: (S.Prog a -> S.Prog a) -> S.Prog a -> S.Prog a
optionalTC tc prog =
  let prog2 = if dbg>0
              then tc prog
              else prog
  in if dbg >= 2
     then trace (" [dbg] engaging optional typecheck pass, AST size "++show(S.progASTSize prog)
                 ++", num binds "++show(length (S.progBinds prog)))
          prog2
     else prog2

--------------------------------------------------------------------------------
-- Misc:
--------------------------------------------------------------------------------

-- instance Show a => Out (Sug.Acc a) where
instance Out (AST.Acc a) where    
  doc       = text . show
  docPrec _ = text . show
