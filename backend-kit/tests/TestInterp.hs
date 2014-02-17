{-# LANGUAGE ScopedTypeVariables #-}

-- | "Test" the main accelerate interpreter.  This is really more a test of the
--   testing infrastructure itself, because the Accelerate interpreter is actually
--   used as the gold standard from which the test "answers" are derived.

module Main where
import Data.Array.Accelerate.BackendKit.Tests (testCompiler, allProgs)
import Data.Array.Accelerate.BackendKit.ConsoleTester 
import Data.Array.Accelerate.BackendClass
import Data.Array.Accelerate.Interpreter as I
import qualified Data.Array.Accelerate.AST as AST

bkend :: MinimalBackend
bkend = MinimalBackend runner

runner :: forall a . Arrays a => AST.Acc a -> a 
runner = I.force . I.evalAcc

main :: IO ()
main = do
       makeMain $ BackendTestConf {
         backend  = bkend,
         sbackend = Nothing,
         knownTests = KnownBad "",
         extraTests = []
       }
