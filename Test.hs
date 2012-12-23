
module Main where

import Data.Array.Accelerate.BackendKit.Tests (testCompiler, allProgs)
import Test.Framework (testGroup, defaultMain)

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as I

main  = defaultMain tests
tests = testCompiler (\ _ p -> I.evalSimpleAcc p) allProgs
