{-# LANGUAGE ScopedTypeVariables #-}

module Data.Array.Accelerate.Cilk.JITRuntime (run, rawRunIO) where 

import           Data.Array.Accelerate (Acc, Arrays)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.OpenCL.JITRuntime as JIT
import           Data.Array.Accelerate.Shared.EmitC (emitC)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase1, phase2, phase3)
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc   as S
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase1, phase2, phase3, repackAcc)

import           System.IO.Unsafe (unsafePerformIO)

--------------------------------------------------------------------------------

-- | Run an Accelerate computation using the OpenCL backend with
--   default (arbitrary) device choice.
run :: forall a . Sug.Arrays a => Acc a -> a
run acc =
  S.maybtrace ("[JIT] Repacking AccArray(s): "++show arrays) $ 
  repackAcc acc arrays
 where
   -- TODO we need a way to reimpose multidimensionality here for this
   -- full "run" interface to work properly.  The LLIR should probably
   -- track the final shape.
--   TArray dim _ = S.progType simple
   simple = phase1 acc
   arrays = unsafePerformIO $
            rawRunIO "" simple

rawRunIO :: String -> S.Prog () -> IO [S.AccArray]
rawRunIO name prog = do
  error "FINISHME - Cilk/JITRuntime.hs"
  

-- This is a mode for running both backends simultaneously:
-- setupAndRunProg Both_C_OpenCL name prog2 = do
--   _ <- setupAndRunProg SeqentialC name prog2
--   setupAndRunProg OpenCL name prog2

-- setupAndRunProg SeqentialC name prog2 = do
--   let emitted = emitC prog2
--       thisprog = ".plainC_"++ stripFileName name
-- -- TODO: Remove file for safety
--   writeFile ".plainC.c" emitted -- Write out this version also.
--   writeFile (thisprog++".c") emitted
--   cd <- system$"gcc -std=c99 "++thisprog++".c -o "++thisprog++".exe"
--   case cd of
--     ExitSuccess -> return ()
--     ExitFailure c -> error$"C Compiler failed with code "++show c
--   ExitSuccess <- system$"./"++thisprog++".exe"
--   return ([],M.empty)

