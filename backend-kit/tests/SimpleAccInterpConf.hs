
module SimpleAccInterpConf (conf, knownProblems) where

-- import Data.Array.Accelerate.BackendKit.Tests (testCompiler, allProgs)
-- import Test.Framework (testGroup, defaultMain)
-- import qualified Data.Array.Accelerate.BackendKit.IRs.CLike.Interpreter as I2
-- import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR.Interpreter as I3
-- import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase2A)
-- import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase2A)
-- import Data.Array.Accelerate.BackendClass

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as I1
import Data.Array.Accelerate.BackendKit.ConsoleTester 

--------------------------------------------------------------------------------

conf :: BackendTestConf
conf = BackendTestConf { 
         backend  = I1.SimpleInterpBackend, 
         sbackend = Nothing,
--         sbackend = Just (SomeSimpleBackend bkend),
         knownTests = KnownBad knownProblems,
         extraTests = [],
         frontEndFusion = False
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
  ++" p10d p10e p10f p10g p10h "   -- Index
  ++" p17a p17b p18d p18e p1bb " -- Backpermute/Reshape, other shapes support
  ++" p20a p20b p20c  " -- Unfinished, fold segs

  -- NOTE! If the debug level is cranked up, four tests fail intermediate typechecks:
  -- ++ " p13c p13d p13f p14e "
  -- For example: 
     -- ERROR: Typecheck pass failed: Unit input expression does not match expected.
     -- Got:      TTuple [TTuple [TInt8,TInt16],TInt32]
     -- Expected: TTuple [TInt8,TInt16,TInt32]
  
  ++ " p5 p13j" -- These are failing for the same reason as in the C backend... new Unit/Z handling, unfinished.

  ++ " p13i "   -- This test passes in C but gets the tuple components flipped in the interp! Bug!


  -- New tests, not supported yet [2014.07.29]:
  ---------------------------------------------
  ++ " p30 p31 p32 p33 p40a p40b p41a p41b "

