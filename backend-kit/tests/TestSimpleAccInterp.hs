
module Main where

import Data.Array.Accelerate.BackendKit.Tests (testCompiler, allProgs)
import Test.Framework (testGroup, defaultMain)

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as I1
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike.Interpreter as I2
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR.Interpreter as I3
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase2A)

import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase2A)

import Data.Array.Accelerate.BackendKit.ConsoleTester 
import Data.Array.Accelerate.BackendClass

--------------------------------------------------------------------------------

-- main  = defaultMain tests
-- tests = testCompiler (\ _ p -> I1.evalSimpleAcc p) allProgs

main :: IO ()
main = do
       makeMain $ BackendTestConf { 
         backend  = I1.interpBackend, 
         sbackend = Nothing,
--         sbackend = Just (SomeSimpleBackend bkend),
         knownTests = KnownBad knownProblems,
         extraTests = []
       }


-- This interepreter is not FINISHED.  Here are the known problems:
knownProblems :: [String]
knownProblems = words $ "" 
  -- Nasty sounding bugs:
  ----------------------------------------
  ++" p1 p1b p2bb " --  ERROR: Ix{Int}.index: Index (10) out of range ((0,9))
  ++" p16c " -- ERROR: zipWith: internal error, input arrays not the same dimension: [10] [5]
  ++" p1ac " -- floating point slightly off: [2.2] vs [2.2183596786e-314]

  -- Simply unfinished:
  ----------------------------------------
  ++" p10d p10e p10f p10g p10h p10i "   -- Index
  ++" p16e p17a p17b p18b p18c p18d p18e p1bb p7 " -- Backpermute/Reshape, other shapes support
  ++" p20a p20b p20c  " -- Unifinished, fold segs

