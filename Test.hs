
module Main where

import Data.Array.Accelerate.SimpleTests (testCompiler, allProgs)
import Test.Framework (testGroup, defaultMain)

import qualified Data.Array.Accelerate.SimpleInterp as I

main  = defaultMain tests
tests = testCompiler (\ _ p -> I.evalSimpleAST p) allProgs
