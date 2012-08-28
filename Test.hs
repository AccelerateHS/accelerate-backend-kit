
module Main where

import Data.Array.Accelerate.SimpleTests (makeTests)
import Test.Framework (testGroup, defaultMain)

import qualified Data.Array.Accelerate.SimpleInterp as I

main  = defaultMain tests
tests = makeTests I.evalSimpleAST
