
-- | Start with the interpreter.  Lift from SimpleBackend to Backend
-- and then Drop back.

module Main where
import Data.Array.Accelerate.BackendKit.ConsoleTester 
import SimpleAccInterpConf (knownProblems)
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as I1
import Data.Array.Accelerate.BackendClass (LiftSimpleBackend(..), DropBackend(..), SomeSimpleBackend(..))

import System.Environment

--------------------------------------------------------------------------------

main :: IO ()
main = do args <- getArgs
          withArgs (args++["--simple"]) $ 
            makeMain conf

conf :: BackendTestConf
conf = BackendTestConf {
         backend  = bkend, 
         sbackend = Just (SomeSimpleBackend (DropBackend bkend)),
--         sbackend = Just (SomeSimpleBackend bkend),
         knownTests = KnownBad knownProblems,
         extraTests = [],
         frontEndFusion = False
       }

bkend :: LiftSimpleBackend I1.SimpleInterpBackend
bkend = LiftSimpleBackend I1.SimpleInterpBackend
