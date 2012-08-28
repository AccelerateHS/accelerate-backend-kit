
module Main where

import Data.Array.Accelerate.SimpleTests (makeTests)
import Test.Framework (testGroup, defaultMain)

import qualified Data.Array.Accelerate.SimpleInterp as I

main  = defaultMain tests
tests = makeTests I.evalSimpleAST

-- tests = [   
--           testCase "convert use/fromList"   (print$ doc t0)
-- 	, testCase "convert fold/zipwith"   (print$ doc t1)
-- 	, testCase "convert map/replicate"  (print$ doc t2)
-- 	, testCase "convert generate/replicate" (print$ doc t3)
-- 	, testCase "convert index scalar"   (print$ doc t4)
-- 	, testCase "convert lift/index"     (print$ doc t5)
-- 	, testCase "convert project tuple"  (print$ doc t6)
-- 	, testCase "convert index test"     (print$ doc t7)
--         , testCase "convert bunch of arith" (print$ doc t8)                              
        --   , testGroup "run p0"  (runBoth p0)
        -- , testGroup "run p1"  (runBoth p1)
        -- , testGroup "run p1a" (runBoth p1a)   -- fromIntegral
        -- , testGroup "run p1aa" (runBoth p1aa)
        -- , testGroup "run p1b" (runBoth p1b)
        -- , testGroup "run p1c" (runBoth p1c)
        -- , testGroup "run p1d" (runBoth p1d)
          
        -- , testGroup "run p2" (runBoth p2)
        -- , testGroup "run p2a" (runBoth p2a)          
        -- , testGroup "run p2b" (runBoth p2b) -- EIndexHeadDynamic
        -- , testGroup "run p2c" (runBoth p2c)
        -- , testGroup "run p2cc" (runBoth p2cc)          
        -- , testGroup "run p2d" (runBoth p2d)
        -- , testGroup "run p2e" (runBoth p2e)
        -- , testGroup "run p2f" (runBoth p2f)          
        -- , testGroup "run p2g" (runBoth p2g)    
        -- , testGroup "run p2h" (runBoth p2h)          
        
        -- , testGroup "run p3" (runBoth p3)  
        -- , testGroup "run p4" (runBoth p4)  
        -- , testGroup "run p4b" (runBoth p4b)  
        -- , testGroup "run p5" (runBoth p5)   
        -- , testGroup "run p6" (runBoth p6)    
        -- , testGroup "run p7" (runBoth p7)      
        -- , testGroup "run p8" (runBoth p8)
        -- , testGroup "run p9" (runBoth p9)
        -- , testGroup "run p9b" (runBoth p9b)
          
        -- , testGroup "run p140" (runBoth p10)          
        -- , testGroup "run p10b" (runBoth p10b)
        -- , testGroup "run p10c" (runBoth p10c)
        -- , testGroup "run p11" $ hUnitTestToTests $ I.run p11 ~=? run p11
        -- , testGroup "run p11b" $ hUnitTestToTests $ I.run p11b ~=? run p11b
        -- , testGroup "run p11c" $ hUnitTestToTests $ I.run p11c ~=? run p11c
        -- , testGroup "run p12" $ hUnitTestToTests $ I.run p12 ~=? run p12
          
        -- , testGroup "run p13" $ hUnitTestToTests $ I.run p13 ~=? run p13                  
        -- , testGroup "run p13b" $ hUnitTestToTests $ I.run p13b ~=? run p13b                   
        -- , testGroup "run p13c" $ hUnitTestToTests $ I.run p13c ~=? run p13c  
        -- , testGroup "run p13d" $ hUnitTestToTests $ I.run p13d ~=? run p13d   
        -- , testGroup "run p13e" $ hUnitTestToTests $ I.run p13e ~=? run p13e   
        -- , testGroup "run p13f" $ hUnitTestToTests $ I.run p13f ~=? run p13f    
        
        -- , testGroup "run p14" $ hUnitTestToTests $ I.run p14 ~=? run p14
        -- , testGroup "run p14b" $ hUnitTestToTests $ I.run p14b ~=? run p14b        
        -- , testGroup "run p14c" $ hUnitTestToTests $ I.run p14c ~=? run p14c        
        -- , testGroup "run p14d" $ hUnitTestToTests $ I.run p14d ~=? run p14d        
        -- , testGroup "run p14e" $ hUnitTestToTests $ I.run p14e ~=? run p14e  -- Won't work until we fix tuple-type ambiguity.  
--         ]
--  where
--   runBoth p = (hUnitTestToTests$ Sug.toList (I.run p) ~=? Sug.toList (run p))

