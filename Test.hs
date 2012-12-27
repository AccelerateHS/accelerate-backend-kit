
-- | The program defined by this module responds to the following ENVIRONMENT VARIABLES:
--  
--  * ALLTESTS=0/1     -- run all tests registered
--  * ONEDIMTESTS=1    -- run one dimensional tests (default 1)
--  * MULTIDIMTESTS=0  -- run multidimensional tests as well as single dimensional ones.
--  * USETESTS=0       -- run tests with Use as well as Generate
--
--  * REPACK=0         -- run tests through the full accelerate wrapper, including repacking the results
--
-- Note that JIT.hs also uses env vars "SIMPLEINTERP", and "EMITC".

module Main where 

import qualified Data.Array.Accelerate             as A
import qualified Data.Array.Accelerate.Interpreter as I
import           Data.Array.Accelerate.BackendKit.Tests (allProgsMap,p1aa,testCompiler,TestEntry(..),AccProg(AccProg),makeTestEntry)
-- import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase1)
import           Data.Map           as M
import           Data.List          as L 
import           Test.Framework     (defaultMain, buildTest, testGroup, Test)
import           Test.Framework.Providers.HUnit (hUnitTestToTests)
import           Test.HUnit         ((~?))
import           System.IO.Unsafe   (unsafePerformIO)
import           Control.Exception  (evaluate)
import           System.Environment (getEnvironment)
import           System.Posix.Env   (getEnv)


import GHC.Conc (threadDelay)
import Debug.Trace        (trace)
import qualified Data.Array.Accelerate.OpenCL.JITRuntime as OpenCL (run,rawRunIO) 
import qualified Data.Array.Accelerate.Cilk.JITRuntime   as Cilk   (run,rawRunIO) 
--------------------------------------------------------------------------------  

main :: IO ()
main = do
  useCBackend <- getEnv "EMITC"
  let backend = case useCBackend of 
                  Just x | notFalse x -> "Cilk"
                  Nothing             -> "OpenCL"
                  _                   -> "OpenCL"
  ----------------------------------------  
  putStrLn "[main] First checking that all requested tests can be found within 'allProgs'..."
  supportedTestNames <- chooseTests
  let manualExamples = [example] -- Here we manually put in additional programs to test.
  let supportedTests = L.filter isCompatible $
        manualExamples ++
        L.map (\ t -> case M.lookup t allProgsMap of 
                        Nothing -> error$"Test not found: "++ show t
                        -- HACK: appending ":" as an end-marker to all test names.  This 
                        -- makes it possible to use the -t pattern matching for all tests.
                        Just (TestEntry nm prg ans orig) -> (TestEntry (nameHack nm) prg ans orig))
              supportedTestNames

      isCompatible (TestEntry name _ _ _)
        | backend == "OpenCL" = True
        | otherwise = if L.elem name useTests
                      then trace ("  (Note: Skipping C backend because "++show name++" is a useTest)")
                                 False
                      else True
        
  -- Force any error messages in spite of lazy data structure:
  if supportedTests == [] then error$ "supportedTestNames should not be null" else return ()
  evaluate (L.foldl1 seq $ L.map (\(TestEntry _ _ _ _) -> ()) supportedTests)
  putStrLn$"[main] Yep, all "++show (length supportedTests)++" tests are there."
  ----------------------------------------  

  let testsPlain = 
       testCompiler (\ name test -> unsafePerformIO$ do
                         let name' = unNameHack name
                         case backend of
                           "OpenCL" -> do
                             x <- OpenCL.rawRunIO name test
                             -- HACK: sleep to let opencl shut down.
                             -- threadDelay 1000000
                             return x
                           "Cilk" -> Cilk.rawRunIO name test
                       )
             supportedTests
  let testsRepack = 
        L.zipWith (\ i (TestEntry name _ _ (AccProg prg)) ->
                    -- let str = show (run OpenCL prg)
                    --     iotest :: IO Test 
                    --     iotest = do putStrLn$ "ACC Result: "++ str
                    --                 return$ testGroup ("run test "++show i++" "++name) $
                    --                         hUnitTestToTests $ 
                    --                           ((length str > 0) ~? "non-empty result string")
                    -- in buildTest iotest

                    let str = show (OpenCL.run prg)
                        iotest :: IO Bool
                        iotest = do putStrLn$ "Repacked: "++ str
                                    return (length str > 0)
                    in testGroup ("run test "++show i++" "++name) $
                       hUnitTestToTests (iotest ~? "non-empty result string")
                  )
        [1..] supportedTests
        
  repack <- getEnv "REPACK"
  case repack of
    Just x | x /= "" && x /= "0" -> defaultMain testsRepack
    _                            -> defaultMain testsPlain


-- | Is an environment variable encoding something representing true.
notFalse ""  = False
notFalse "0" = False
notFalse _   = True

nameHack :: String -> String
nameHack = (++":")

unNameHack :: String -> String
unNameHack = init 

-- | Use the environment to decide which set of tests we are running:
chooseTests :: IO [String]
chooseTests = do
  env <- getEnvironment
  let tests1 = case L.lookup "ONEDIMTESTS" env of
                 Nothing             -> oneDimOrLessTests -- Default ON
                 Just x | notFalse x -> oneDimOrLessTests
                 _                   -> []
  let tests2 = case L.lookup "USETESTS" env of
                 Just x | notFalse x -> useTests
                 _                   -> []
  let tests3 = case L.lookup "MULTIDIMTESTS" env of
                 Just x | notFalse x -> multiDimTests
                 _                   -> []
  case L.lookup "ALLTESTS" env of
    Just _  -> return$ oneDimOrLessTests ++ useTests ++ multiDimTests ++ highDimTests    
    Nothing -> return$ tests1 ++ tests2 ++ tests3


example :: TestEntry
example = makeTestEntry "example" p
 where
   p :: A.Acc (A.Scalar Int)
   p = A.unit 3 

oneDimOrLessTests :: [String]
oneDimOrLessTests = words$ 
     " p1a p1aa p1ab p1ac p1ba  "
  ++ " p2 "                   -- These will push map through replicate     
  ++ " p2a  p2e p2f "    -- Some simple replicates
  ++ " p16a p16b p16c p16d"
  ++ " p16e"                   -- has a map that won't get fused; gets desugared to Generate.
  ++ " p4 p4c"                     -- scalar indexing
  ++ " p6b"                    -- scalar tuples
--  ++ " p9a p9b p9c"            -- array of tuples    
  ++ " p10c p10d p10e p10f p10g p10h p10i "  -- uses slice/index
  ++ " p11 p11b p11c  "                      -- tuples of arrays
  ++ " p12 p12b p12c p12d p12e"              -- array and scalar conditionals
  ++ " p17a "                                -- uses trivial reshape
  ++ " p18a p18b p18d p18e p18f "            -- dynamically sized array

  ++ " p1 " -- This adds a FOLD.

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
  "p17b "


-- | Four dimensional and above.
highDimTests :: [String]
highDimTests = words$ 
  " p18c " ++ -- This internally uses an array-of-tuples but it ends up being dead code.
  " p2i  "

------------------------------------------------------------
-- Tests we can't handle yet:
------------------------------------------------------------
-- p1b  -- requires fold

-- These tests are waiting on arrays of tuples:
-- p1d p6 
-- p2g  p2h
--  "p2d "++ -- requires array-of-tuple AND >3D 

