{-# LANGUAGE CPP, ExistentialQuantification #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Build a console test runner for any instance of the Backend class.

module Data.Array.Accelerate.BackendKit.ConsoleTester 
       (  BackendTestConf(..), KnownTests(..), 
          makeMain
       )
       where 

import           Control.Exception
import           Control.Monad (when, unless)
import qualified Data.Array.Accelerate             as A
import           Data.Array.Accelerate.Trafo.Sharing (convertAcc)
import           Data.Array.Accelerate.Trafo (convertAccWith, Phase(..))
import           Data.Array.Accelerate.BackendKit.Tests (allProgs,allProgsMap,testCompiler,TestEntry(..),
                                                         AccProg(AccProg),makeTestEntry)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1, phase2, repackAcc)
-- import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase1)
import qualified Data.Array.Accelerate.BackendClass as BC

import           Data.Map           as M
import           Data.Set           as Set
import           Data.List          as L
import           Data.Char          (toLower)
import           Test.Framework     (defaultMain, buildTest, testGroup, Test, optionsDescription)
import           Test.Framework.Providers.HUnit (hUnitTestToTests, testCase)
import           Test.HUnit         ((~?))
import           Test.HUnit as HU
import           System.IO.Unsafe   (unsafePerformIO)
import           System.Environment (getEnvironment, getArgs, withArgs)
import           System.Console.GetOpt

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SimpleAcc

import GHC.Conc (threadDelay)
import Debug.Trace        (trace)
--------------------------------------------------------------------------------  

-- | Everything needed to run tests for a given backend.
data BackendTestConf =
     forall b . (BC.Backend b) => BackendTestConf 
     { backend :: b
     , sbackend :: Maybe (BC.SomeSimpleBackend) -- ^ Optional SimpleBackend alternative instance, for use when --simple is passed.
     , knownTests :: KnownTests  -- ^ Which of the standard tests (Tests.allProgs) should this backend pass?
     , extraTests :: [TestEntry] -- ^ Additional tests for this backend.
     , frontEndFusion :: Bool    -- ^ Allow the Accelerate front-end to perform fusion optimizations
     }

-- | We describe the current expected level of functionality from a given backend by
-- listing either the known-good or known-bad tests by name.  All /unlisted/ tests are
-- assumed to fall into the opposite bucket.
data KnownTests = KnownGood [String]
                | KnownBad [String]

knownNames (KnownGood ls) = ls
knownNames (KnownBad ls) = ls

data Flag = Help | UseSimple     deriving (Eq,Ord,Show,Read)

options :: [OptDescr Flag]
options =
     [ Option ['h'] ["help"] (NoArg Help)              "report this help message"
--     , Option [] ["norepack"]  (NoArg UseSimple)  "do NOT run tests through the full accelerate wrapper, repacking the results"
     , Option [] ["simple"]  (NoArg UseSimple) "do not repack results as full Accelerate arrays, rather use the SimpleAcc and AccArray representations only"
     ]

makeMain :: BackendTestConf -> IO ()
makeMain BackendTestConf{backend,sbackend,knownTests,extraTests,frontEndFusion} = do
 args <- getArgs
 let (opts,nonopts,unrecog,errs) = getOpt' Permute options args
 -- let (opts,nonopts,errs) = getOpt Permute options args 
 let help1 = usageInfo ("USAGE: test-accelerate-cpu-* [options]\n"++
                       "\nFirst, specific options for test harness are:\n"++
                       "---------------------------------------------\n")
               options
     help2 = usageInfo (help1++"\nAlso use the generic test-framework options below:\n"++
                       "--------------------------------------------------\n")
                       optionsDescription 
 if Help `elem` opts || errs /= [] then error help2
  else do
   let passthru = unrecog ++ nonopts 
   -- let passthru = args
   putStrLn$ "  [Note: passing through options to test-framework]: "++unwords passthru
   withArgs passthru $ do 
    ------------------------------------------------------------  
    putStrLn$ " [!] Testing backend: "++ show backend
    ----------------------------------------  
    putStrLn "[main] First checking that all named tests can be found within 'allProgs'..."
    let allMentioned = Set.fromList $ knownNames knownTests
    let notFound     = Set.difference allMentioned (M.keysSet allProgsMap)
    let notMentioned = Set.toList$ Set.difference (M.keysSet allProgsMap) allMentioned                                              
    unless (Set.null notFound) $ 
      error $ "Referred to test cases not found (by name) in allProgs: "++show (Set.toList notFound)
    let goods, bads :: [String]
        (goods,bads) = case knownTests of 
                        KnownGood ls -> (ls, notMentioned)
                        KnownBad  ls -> (notMentioned, ls)
    let goodEntries = L.map (nameHackTE . (allProgsMap M.!)) goods
        badEntries  = L.map (nameHackTE . (allProgsMap M.!)) bads
    -- Laziness...
    mapM_ evaluate goodEntries
    mapM_ evaluate badEntries
    putStrLn$"[main] Yep, all mentioned tests are there."
    ----------------------------------------  
    -- let rawComp name test = 
    --       case themode of
    --         Cilk        -> JIT.rawRunIO CilkParallel name (phase2 test)
    --         SequentialC -> JIT.rawRunIO Sequential   name (phase2 test)
    --         OpenCL      -> rawRunOpenCL name test 
    -- let testsPlain = testCompiler (\ name test -> unsafePerformIO$ rawComp name test) supportedTests

    let testsRepack = 
          L.zipWith (\ i (TestEntry { name, origProg=(AccProg prg), interpResult }) ->
                      let str = show (runWith backend frontEndFusion  (Just name) prg)
                      in testCase ("run test "++show i++"/"++show (length goodEntries)++" "++name) $ 
                         assertEqual "Printed Accelerate result should match expected" 
                                               interpResult str
                    )
          [1::Int ..] goodEntries

    let testsRepackBad = 
          L.zipWith (\ i (TestEntry { name, origProg=(AccProg prg), interpResult }) ->
                      testCase ("expected-to-fail test "++show i++"/"++show (length badEntries)++" "++name) $
                      assertException [""] $ 
                       let str = show (runWith backend frontEndFusion  (Just name) prg) 
                       in unless (interpResult == str) $ 
                           error $ "Printed Accelerate result should match expected:\n Expected: "
                                   ++interpResult++"\n Got: "++str++"\n"
                    )
          [1::Int ..] badEntries

    let testsSimple = 
          L.zipWith (\ ix (TestEntry { name, simpleProg, simpleResult }) -> 
                      case sbackend of
                        Nothing -> error "Cannot run in --simple mode without BackendTestConf.sbackend provided!"
                        Just (BC.SomeSimpleBackend sback) -> 
                         testCase ("run test [simple mode] "++show ix++"/"++show (length goodEntries)++" "++name) $ do 
                           ls <- BC.simpleRunRaw sback (Just name) simpleProg Nothing
                           ls2 <- mapM (BC.simpleCopyToHost sback) ls 
                           let str = show $ concat $ L.map SimpleAcc.arrPayloads ls2
                           assertEqual "[simple] Printed Accelerate result should match expected" 
                                       simpleResult str
                    )
          [1::Int ..] goodEntries
    let testsSimpleBad = 
          L.zipWith (\ ix (TestEntry { name, simpleProg, simpleResult }) -> 
                      case sbackend of
                        Nothing -> error "Cannot run in --simple mode without BackendTestConf.sbackend provided!"
                        Just (BC.SomeSimpleBackend sback) -> 
                         testCase ("expected-to-fail test [simple mode] "++show ix++"/"++show (length badEntries)++" "++name) $ 
                         assertException [""] $ do
                           ls <- BC.simpleRunRaw sback (Just name) simpleProg Nothing
                           ls2 <- mapM (BC.simpleCopyToHost sback) ls 
                           let str = show $ concat $ L.map SimpleAcc.arrPayloads ls2
                           unless (simpleResult == str) $
                             error$ "[simple] Printed Accelerate result should match expected.\nExpected: "
                                    ++simpleResult++"\nGot: "++str++"\n"
                    )
          [1::Int ..] badEntries

    if UseSimple `elem` opts 
     then defaultMain (testsSimple ++ testsSimpleBad)
     else defaultMain (testsRepack ++ testsRepackBad)
    putStrLn " [Test.hs] You will never see this message, because test-framework defaultMain exits the process."


-- | Run a complete Accelerate program through the front-end, and the given backend.
--   Optionally takes a name associated with the program.
runWith :: (BC.Backend b, A.Arrays a) => b -> Bool -> Maybe String -> A.Acc a -> a
runWith bkend frontEndFusion nm prog = unsafePerformIO $ do 
--  let cvtd = convertAcc True True True prog
  let cvtd = phase0 prog
--  let cvtd = convertAccWith config prog
      -- config = Phase
      --          { recoverAccSharing      = True
      --          , recoverExpSharing      = True
      --          , floatOutAccFromExp     = True
      --          , enableAccFusion        = frontEndFusion
      --          , convertOffsetOfSegment = True
      --          }
  remote <- BC.runRaw bkend cvtd Nothing 
  BC.copyToHost bkend remote


-- Add an extra terminating character to make the "-t" command line option more
-- useful for selecting tests.
nameHack :: String -> String
nameHack = (++":")

nameHackTE :: TestEntry -> TestEntry
nameHackTE (te@TestEntry{name}) = te { name = nameHack name }

unNameHack :: String -> String
unNameHack = init 

------------------------------------------------------------
-- Helpers copied from elsewhere:
------------------------------------------------------------

-- | Ensure that executing an action returns an exception
-- containing one of the expected messages.
assertException  :: [String] -> IO a -> IO ()
assertException msgs action = do
 x <- catch (do action; return Nothing) 
            (\e -> do putStrLn $ "Good.  Caught exception: " ++ show (e :: SomeException)
                      return (Just $ show e))
 case x of 
  Nothing -> HU.assertFailure "Failed to get an exception!"
  Just s -> 
   if  any (`isInfixOf` s) msgs
   then return () 
   else HU.assertFailure $ "Got the wrong exception, expected one of the strings: "++ show msgs
        ++ "\nInstead got this exception:\n  " ++ show s

