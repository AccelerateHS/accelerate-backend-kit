
module Main where

import Data.Array.Accelerate.BackendKit.Tests (testCompiler, allProgs)
import Test.Framework (testGroup, defaultMain)

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as I1
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike.Interpreter as I2
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR.Interpreter as I3
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase2A)

main  = defaultMain tests

-- tests = testCompiler (\ _ p -> I1.evalSimpleAcc (phase2A p)) allProgs
tests = testCompiler (\ _ p -> I1.evalSimpleAcc p) allProgs
