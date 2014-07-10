-- {-# LANGUAGE CPP, NamedFieldPuns #-}

-- | Start with the C backend.  Lift from SimpleBackend to Backend
-- and then Drop back.

module Main where 

import Data.Array.Accelerate.BackendKit.ConsoleTester 
import Data.Array.Accelerate.BackendClass (SomeSimpleBackend(..), DropBackend(..))
-- import qualified Data.Array.Accelerate.Cilk as Cilk
import qualified Data.Array.Accelerate.C    as C
import System.Environment

--------------------------------------------------------------------------------

bkend :: C.CBackend
bkend = C.CBackend

main :: IO ()
main = do args <- getArgs
          withArgs (args++["--simple"]) $ 
            makeMain conf

conf :: BackendTestConf
conf = BackendTestConf { 
         backend  = bkend,
         sbackend = Just (SomeSimpleBackend (DropBackend bkend)),
--         knownTests = KnownGood allTests,
         knownTests = KnownBad knownProblems,
         extraTests = [],
         frontEndFusion = False
       }

knownProblems :: [String]
knownProblems = words $ "" 
  ++ " p5 p13j " 
  -- UNFINISHED, not bugs:
  ----------------------------------------
  ++ " p20a p20b p20c " -- UNFINISHED error printed, strides for foldsegs [2014.02.16]

  -- [2014.02.27] New breakage from reglueArrayofTups, need to come back to:
  ++ " p13k p13i "

  -- Scan programs
  ++ " p30 p31" 
