{-# LANGUAGE CPP, NamedFieldPuns #-}

-- | The program defined by this module responds to various command line flags.
--  
-- Also, note that  JIT.hs responds to env vars "SIMPLEINTERP", and "EMITC".

module Main where 

import           Data.Array.Accelerate.BackendKit.ConsoleTester 
import           Data.Array.Accelerate.BackendClass (SomeSimpleBackend(..))
import           System.Process(system)
import qualified Data.Array.Accelerate.Cilk as Cilk
import qualified Data.Array.Accelerate.C    as C

#ifdef USECILK
bkend = Cilk.CilkBackend
#else
bkend = C.CBackend
#endif


main :: IO ()
main = do 
       -- system "rm -rf .genC_*" -- Remove remaining output from last time, if any
       makeMain $ BackendTestConf { 
         backend  = bkend,
         sbackend = Just (SomeSimpleBackend bkend),
--         knownTests = KnownGood allTests,
         knownTests = KnownBad knownProblems,
         extraTests = [],
         frontEndFusion = False
       }

knownProblems :: [String]
knownProblems = words $ "" 
  -- These pass in --simple mode, but are having a problem in the repacking phase:
  ----------------------------------------
  ++ "p13 p13b p13c p13d p13e p13f p14 p14b p14e "
  ++ "p9c "
  ++ "p1d p2d p2g p2h p9a p9b " -- Tuple components flipped during repack!! [2014.02.16]

  -- Wrong answers, even in --simple:
  ----------------------------------------
  -- ++ " p12 " -- Bad answer, number 40 turned to 0 or 2!  Egad, nondeterministic!  Sometimes works.
  ++ " p8 " -- Bad result even in --simple!  Returns 2*pi instead of pi. [2014.02.16]

  -- UNFINISHED, not bugs:
  ----------------------------------------
  ++ " p20a p20b p20c " -- UNFINISHED error printed, strides for foldsegs [2014.02.16]



--------------------------------------------------------------------------------  
-- OLD: switching away from enumerating working cases
--------------------------------------------------------------------------------  

knownGood = oneDimOrLessTests ++ useTests ++ multiDimTests ++ highDimTests

oneDimOrLessTests :: [String]
oneDimOrLessTests = words$ 
     " p1a p1aa p1ab p1ac p1ba  "
  ++ " p2 "                    -- These will push map through replicate     
  ++ " p2a  p2e p2f "          -- Some simple replicates
  ++ " p16a p16b p16c p16d"
  ++ " p16e"                   -- Has a map that won't get fused; gets desugared to Generate.
  ++ " p4 p4c"                 -- scalar indexing
  ++ " p6b"                    -- scalar tuples
--  ++ " p9a p9b p9c"            -- array of tuples    
  ++ " p10c p10d p10e p10f p10g p10h p10i "  -- uses slice/index
  ++ " p11 p11b p11c  "                      -- tuples of arrays
  ++ " p12 p12b p12c p12d p12e"              -- array and scalar conditionals
  ++ " p17a "                                -- uses trivial reshape
  ++ " p18a p18b p18d p18e p18f "            -- dynamically sized array

  ++ " p1 " -- This adds a FOLD.
  ++ " p1d p6 " -- Array of tuples

-- These tests are waiting on arrays of tuples:

  -- DUMPING these in, go through them:
  ++ "p5 p8 p9a p9b  p14d p14c "
  -- p9c p13 p14e

  -- Scalar tuples and projection:
  -- KNOWN problems with tuple packing presently:
  -- ++ "p13 p13b p13c p13d p13e p13f p14 p14b p14e "
  -- ++ "p9c"

useTests :: [String]
useTests = words$ 
  " p0 p1c " ++
  -- These are ALSO multidim:
  " p7 "

-- | Two and three dimensional tests.
multiDimTests :: [String]
multiDimTests = words$ 
  "p2aa p2bb " ++ 
  "p2b p2c p2cc p2cd p2ce "++ -- a Replicate with an 'All'.   
  "p3 p4b " ++
  "p10 p10b " ++ 
  "p17b " ++
--  "p20a p20b p20c " ++  -- fold1seg
  "p1b p1bb "++ -- fold 2D to 1D
  "p2g p2h " -- Multidim and array-of-tuple

-- | Four dimensional and above.
highDimTests :: [String]
highDimTests = words$ 
  " p18c " ++ -- This internally uses an array-of-tuples but it ends up being dead code.
  " p2i  "++
   "p2d " -- requires array-of-tuple AND >3D

   
