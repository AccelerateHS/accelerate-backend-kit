{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.Array.Accelerate.SimpleConverter (convertToSimpleAST)
import qualified Data.Array.Accelerate.SimpleAST    as S
import qualified Data.Array.Accelerate.SimpleInterp as I
-- import qualified Data.Array.Accelerate.Smart       as Sugar
-- import qualified Data.Array.Accelerate.Array.Sugar as Sugar
import qualified Data.Array.Accelerate.Array.Sugar as Sug

import Data.Int
-- import Data.Array.Accelerate (use,Z,(:.))
-- import qualified Data.Array.Accelerate as Acc
import Data.Array.Accelerate as A 
import Data.Array.Accelerate.Interpreter

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit 
import Data.List       (intersperse)
import Data.List.Split (splitEvery)

-- TEMP:
-- import qualified Data.Array.Accelerate.Language as Lang
-- TEMP:
-- import qualified Data.Array.Accelerate.Interpreter as Interp
import Text.PrettyPrint.GenericPretty (doc)
import Prelude hiding (zipWith,replicate,map)
import qualified Prelude as P

p0 = use $ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Int64]
t0 :: S.AExp
t0 = convertToSimpleAST p0
r0 = I.run p0

-- | Sharing recovery will create a Let here:
p1 :: Acc (Scalar Float)
p1 = fold (+) 0 (zipWith (*) p1a p1a)
t1 :: S.AExp
t1 = convertToSimpleAST p1
r1 = I.run p1

-- | Just generate:
p1a :: Acc (Vector Float)
p1a = generate (constant (Z :. (10::Int))) 
       (A.fromIntegral . unindex1) 
      --(\ (i) -> 3.3 )

-- | And again with a 2D array:
p1b :: Acc (Vector Float)
p1b = let xs = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
      in  fold (+) 0 xs
t1b :: S.AExp
t1b = convertToSimpleAST p1b
r1b = I.run p1b


-- This one is JUST a zipwith:
p1c :: Acc (Vector Word)
p1c = let xs = use$ fromList (Z :. (5::Int)) [1..10::Word] 
      in zipWith (*) xs xs
  
-- Zipwith yielding a tuple:
p1d :: Acc (Vector (Word,Word))
p1d = let xs = use$ fromList (Z :. (5::Int)) [1..10::Word] 
      in zipWith (\ x y -> lift (x*y, x+y)) xs xs


----------------------------------------

p2 :: Acc (Vector Int32)
p2 = let xs = replicate (constant (Z :. (4::Int))) (unit 40)
     in map (+ 10) xs
t2 = convertToSimpleAST p2
r2 = I.run p2

p2a :: Acc (Scalar Word)
p2a = unit 40

p2b :: Acc (Array DIM2 Int)
p2b = let arr = generate (constant (Z :. (5::Int))) unindex1
--      in replicate (constant$ Z :. (4::Int) :. All) arr
      in replicate (constant$ Z :. All :. (4::Int)) arr
          -- 1st generates: Array (Z :. 4 :. 5) [0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4]
          -- 2nd generates: Array (Z :. 5 :. 4) [0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4]
t2b = convertToSimpleAST p2b

p2c :: Acc (Array DIM3 Int)
p2c = let arr = generate (constant (Z :. (3::Int) :. (3::Int))) 
                         (\e -> let (r,c) = unlift$ unindex2 e in 3 * r + c)
      in replicate (constant$ Z :. All :. (2::Int) :. All) arr
--      in replicate (constant$ Z :. All :. All :. (2::Int)) arr  

p2d :: Acc (Array DIM4 (Int,Int))
p2d = let arr = generate (constant (Z :. (3::Int) :. (3::Int))) unindex2
      in replicate (constant$ Z :. All :. (2::Int) :. All :. (2::Int)) arr


p2e :: Acc (Array DIM1 Int)
p2e = let arr = generate (constant (Z :. (5::Int))) unindex1
      in replicate (constant$ Z :. All) arr

p2f :: Acc (Array DIM0 Int)
p2f = let  arr = unit (constant 33)
      in replicate (constant$ Z) arr

--------------------------------------------------------------------------------

p3 :: Acc (Array DIM3 Int32)
p3 = let arr = generate  (constant (Z :. (5::Int))) (\_ -> 33)
         xs  = replicate (constant$ Z :. (2::Int) :. All :. (3::Int)) arr
     in xs 
t3 = convertToSimpleAST p3
r3 = I.run p3

-- Test 4, a program that creates an IndexScalar:
p4 :: Acc (Scalar Int64)
p4 = let arr = generate (constant (Z :. (5::Int))) (\_ -> 33) in
     unit $ arr ! (index1 2)
        -- (Lang.constant (Z :. (3::Int)))  
t4 = convertToSimpleAST p4         
r4 = I.run p4

p4b :: Acc (Scalar Int64)
p4b = let arr = generate (constant (Z :. (3::Int) :. (3::Int))) (\_ -> 33) 
              :: Acc (Array DIM2 Int64)
      in
     unit $ arr ! (index2 1 2)
t4b = convertToSimpleAST p4b


-- This one generates EIndex:
p5 :: Acc (Scalar (((Z :. All) :. Int) :. All))
p5 = unit$ lift $ Z :. All :. (2::Int) :. All
t5 = convertToSimpleAST p5
r5 = I.run p5

-- This one generates ETupProjectFromRight:
p6 :: Acc (Vector Float)
p6 = map go (use xs)
  where
    xs :: Vector (Float, Float)
    xs = fromList sh [(1,10),(2,20)]
    sh = Z :. (2::Int)
    go x = let (a,b) = unlift x   in a*b
t6 = convertToSimpleAST p6
r6 = I.run p6

transposeAcc :: Array DIM2 Float -> Acc (Array DIM2 Float)
transposeAcc mat =
  let mat' = use mat
      swap = lift1 $ \(Z:.x:.y) -> Z :.      y  :.      x 
                                :: Z :. Exp Int :. Exp Int
  in
  backpermute (swap $ shape mat') swap mat'

-- This one uses dynamic index head/tail (but not cons):
p7 :: Acc (Array DIM2 Float)
p7 = transposeAcc (fromList (Z :. (2::Int) :. (2::Int)) [1..4])
t7 = convertToSimpleAST p7
r7 = I.run p7
-- Evaluating "doc t7" prints:
-- Let a0
--     (TArray TFloat)
--     (Use "Array (Z :. 2) :. 2 [1.0,2.0,3.0,4.0]")
--     (Backpermute (EIndex [EIndexHeadDynamic (EIndexTailDynamic (EShape (Vr a0))),
--                           EIndexHeadDynamic (EShape (Vr a0))])
--                  (Lam [(v1, TTuple [TInt,TInt])]
--                       (EIndex [EIndexHeadDynamic (EIndexTailDynamic (EVr v1)),
--                                EIndexHeadDynamic (EVr v1)]))
--                  (Vr a0))

-- TODO -- still need to generate an IndexCons node.

----------------------------------------

-- This shows an odd difference in staging:
p8 :: Acc (Scalar Float)
p8 = unit$ pi + (constant pi :: Exp Float) *
           negate (negate (abs (signum pi)))

t8 = convertToSimpleAST p8
r8 = I.run p8

-- Prim arguments don't need to directly be tuple expressions:
-- unit ((+) (let x0 = pi in (x0, 3.1415927 * x0)))



-- A map with a tuple return type:
p9 :: Acc (Vector (Int32,Int32))
p9 = let xs = replicate (constant (Z :. (4::Int))) (unit 40)
     in map (\ x -> lift (x+10, x*10)) xs

-- How about tuples coming in and going out:
p9b :: Acc (Vector (Int32,Int32,Int32))
p9b = map (\ e ->  
                  let (x,y) = unlift e in 
--                  (x::Exp Int32) + (y::Exp Int32)
                  lift (x::Exp Int32, y::Exp Int32, x+y)
          )
          p9
 
--------------------------------------------------------------------------------
-- Let's print matrices nicely.

padleft n str | length str >= n = str
padleft n str | otherwise       = P.take (n - length str) (repeat ' ') ++ str

class NiceShow a where
  pp :: a -> String
        
instance Show a => NiceShow (Array DIM1 a) where
  pp arr = 
    capends$ concat$ 
    intersperse " " $
    P.map (padleft maxpad) ls 
   where 
         ls   = P.map show $ toList arr
         maxpad = maximum$ P.map length ls

capends x = "| "++x++" |"

-- This could be much more efficient:
instance Show a => NiceShow (Array DIM2 a) where
  pp arr = concat $
           intersperse "\n" $ 
           P.map (capends . 
                  concat . 
                  intersperse " " . 
                  P.map (padleft maxpad)) 
            rowls
   where (Z :. rows :. cols) = arrayShape arr
         ls   = P.map show $ toList arr
         maxpad = maximum$ P.map length ls
         rowls = splitEvery cols ls


--------------------------------------------------------------------------------

main = defaultMain tests
tests = [ testCase "use/fromList"   (print$ doc t0)
	, testCase "fold/zipwith"   (print$ doc t1)
	, testCase "map/replicate"  (print$ doc t2)
	, testCase "generate/replicate" (print$ doc t3)
	, testCase "index scalar"   (print$ doc t4)
	, testCase "lift/index"     (print$ doc t5)
	, testCase "project tuple"  (print$ doc t6)
	, testCase "index test"     (print$ doc t7)
        , testCase "bunch of arith" (print$ doc t8)
                    
          
        , testGroup "run p0"  (runBoth p0)
        , testGroup "run p1"  (runBoth p1)
        , testGroup "run p1a" (runBoth p1a)
        , testGroup "run p1b" (runBoth p1b)
        , testGroup "run p1c" (runBoth p1c)
        , testGroup "run p1d" (runBoth p1d)
          
        , testGroup "run p2" (runBoth p2)
        , testGroup "run p2a" (runBoth p2a)
          
--        , testGroup "run p2b" (runBoth p2b) -- EIndexHeadDynamic
          
        , testGroup "run p8" (runBoth p8)
        , testGroup "run p9" (runBoth p9)
        , testGroup "run p9b" (runBoth p9b)
        ]
 where
  runBoth p = (hUnitTestToTests$ Sug.toList (I.run p) ~=? Sug.toList (run p))

-- main = print (I.run p8)
