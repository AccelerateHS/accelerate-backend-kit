{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.Array.Accelerate.SimpleConverter (convertToSimpleAST, convertToSimpleProg)
import qualified Data.Array.Accelerate.SimpleAST    as S
import qualified Data.Array.Accelerate.SimpleInterp as I
import qualified Data.Array.Accelerate.Smart       as Sm
import qualified Data.Array.Accelerate.Tuple       as Tu
-- import qualified Data.Array.Accelerate.Array.Sugar as Sugar
import qualified Data.Array.Accelerate.Array.Sugar as Sug

import Data.Int
-- import Data.Array.Accelerate (use,Z,(:.))
-- import qualified Data.Array.Accelerate as Acc
import Data.Array.Accelerate as A 
import Data.Array.Accelerate.Interpreter

import Test.Framework (testGroup, defaultMain)
import Test.Framework.Providers.HUnit
import Test.HUnit      ((~=?))
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
t0 = convertToSimpleProg p0
r0 = I.run p0

-- | Sharing recovery will create a Let here:
p1 :: Acc (Scalar Int)
p1 = fold (+) 0 (zipWith (*) p1aa p1aa)
t1 = convertToSimpleProg p1
r1 = I.run p1

-- | Just generate 
p1aa :: Acc (Vector Int)
p1aa = generate (constant (Z :. (10::Int)))
       (unindex1)

-- | Also exercise fromIntegral:
p1a :: Acc (Vector Float)
p1a = generate (constant (Z :. (10::Int))) 
       (A.fromIntegral . unindex1) 


-- | And again with a 2D array:
p1b :: Acc (Vector Float)
p1b = let xs = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
      in  fold (+) 0 xs
t1b = convertToSimpleProg p1b
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
t2 = convertToSimpleProg p2
r2 = I.run p2

p2a :: Acc (Scalar Word)
p2a = unit 40

p2b :: Acc (Array DIM2 Int)
p2b = let arr = generate (constant (Z :. (5::Int))) unindex1
--      in replicate (constant$ Z :. (4::Int) :. All) arr
      in replicate (constant$ Z :. All :. (4::Int)) arr
          -- 1st generates: Array (Z :. 4 :. 5) [0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4]
          -- 2nd generates: Array (Z :. 5 :. 4) [0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4]
t2b = convertToSimpleProg p2b

-- | A 2D array with some tuple operations:
p2c :: Acc (Array DIM2 Int)
p2c = generate (constant (Z :. (3::Int) :. (3::Int)))
               (\e -> let (r,c) = unlift$ unindex2 e in 3 * r + c)

-- | Expand 2D -> 3D
p2cc :: Acc (Array DIM3 Int)
p2cc = replicate (constant$ Z :. All :. (2::Int) :. All) p2c
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

-- | Similar to p2c, except now simply return indices:
p2g :: Acc (Array DIM2 (Int,Int))
p2g = generate (constant (Z :. (3::Int) :. (3::Int))) unindex2

p2h :: Acc (Array DIM3 (Int,Int))
p2h = replicate (constant$ Z :. All :. (2::Int) :. All) p2g


--------------------------------------------------------------------------------

p3 :: Acc (Array DIM3 Int32)
p3 = let arr = generate  (constant (Z :. (5::Int))) (\_ -> 33)
         xs  = replicate (constant$ Z :. (2::Int) :. All :. (3::Int)) arr
     in xs 
t3 = convertToSimpleProg p3
r3 = I.run p3

-- Test 4, a program that creates an IndexScalar:
p4 :: Acc (Scalar Int64)
p4 = let arr = generate (constant (Z :. (5::Int))) (\_ -> 33) in
     unit $ arr ! (index1 2)
        -- (Lang.constant (Z :. (3::Int)))  
t4 = convertToSimpleProg p4         
r4 = I.run p4

p4b :: Acc (Scalar Int64)
p4b = let arr = generate (constant (Z :. (3::Int) :. (3::Int))) (\_ -> 33) 
              :: Acc (Array DIM2 Int64)
      in
     unit $ arr ! (index2 1 2)
t4b = convertToSimpleProg p4b


-- This one generates EIndex. It creates an array containing a slice descriptor.
p5 :: Acc (Scalar (((Z :. All) :. Int) :. All))
p5 = unit$ lift $ Z :. All :. (2::Int) :. All
t5 = convertToSimpleProg p5
r5 = I.run p5

-- This one generates ETupProjectFromRight:
p6 :: Acc (Vector Float)
p6 = map go (use xs)
  where
    xs :: Vector (Float, Float)
    xs = fromList sh [(1,10),(2,20)]
    sh = Z :. (2::Int)
    go x = let (a,b) = unlift x   in a*b
t6 = convertToSimpleProg p6
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
t7 = convertToSimpleProg p7
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

t8 = convertToSimpleProg p8
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
-- How do we create IndexAny?

-- repN :: Int -> Array sh e -> Acc (Array (sh:.Int) e)
-- repN n a = replicate (Any :. n) a

repN :: (Shape sh, Elt e) => Int -> Acc (Array sh e) -> Acc (Array (sh:.Int) e)
repN n a = replicate (constant$ Any :. n) a

p10 :: Acc (Array DIM1 Float)
p10 = repN 3 (unit 40.4)

p10b :: Acc (Array DIM2 Float)
p10b = repN 4 p10

p10c :: Acc (Array DIM1 Float)
p10c = replicate (constant$ Any :. (3::Int)) (unit 4.4)

----------------------------------------

-- How about tuples of arrays?
p11 :: Acc (Scalar Int, Scalar Int16, Scalar Int32)
p11 = lift (unit 1, unit 2, unit 3)

p11b :: Acc (Scalar Int, Scalar Int32)
p11b = let (a,b,c) = unlift p11 
                     :: (Acc (Scalar Int), Acc (Scalar Int16), Acc (Scalar Int32)) 
                     -- NOTE!  Should this ^^ type annotation REALLY be necessary?
                     -- Is there no way to further constrain the mechanism here?
                     -- Are there really other viable intermediate types here?
       in lift (a,c)


p11c :: Acc ((Scalar Int, Scalar Int32),(Scalar Int, Scalar Int32))
p11c = lift (p11b,p11b)
--       in lift (a,c)    
--           new     = lift (a,c)
--       in lift (new,new)

p12 :: Acc (Scalar Word32, Scalar Float)
p12 = let arr = generate (constant (Z :. (5::Int))) unindex1 in 
      cond (arr A.! (index1 2) >* 2)
           (lift (unit 10, unit 20.0))
           (lift (unit 40, unit 30.0))

--------------------------------------------------------------------------------
-- Let's test tuple type conversion

p13 :: Acc (Scalar ((Int8,Int16),(Int32,Int64)))
p13 = unit $ 
      Sm.tup2 ((Sm.tup2 (constant (1::Int8),  constant (2::Int16))),
               (Sm.tup2 (constant (3::Int32), constant (4::Int64))))

p13b :: Acc (Scalar (Int8,Int16,Int32))
p13b = unit p13b_
p13b_ = 
      Sm.tup3 (constant (1::Int8),  
               constant (2::Int16),
               constant (3::Int32))

p13c :: Acc (Scalar ((Int8,Int16),Int32))
p13c = unit p13c_
p13c_ = 
      Sm.tup2 ((Sm.tup2 (constant (1::Int8),  constant (2::Int16))),
               (constant (5::Int32)))


p13d :: Acc (Scalar ((Int8,Int16),(Int32,Int64),(Float,Double)))
p13d = unit $ 
      Sm.tup3 ((Sm.tup2 (constant (1::Int8),  constant (2::Int16))),
               (Sm.tup2 (constant (3::Int32), constant (4::Int64))),
               (Sm.tup2 (constant (5::Float), constant (6::Double))))

p13e :: Acc (Scalar (((Int8,Int16),(Int32,Int64)),(Float,Double)))
p13e = unit $ 
      Sm.tup2 (Sm.tup2 ((Sm.tup2 (constant (1::Int8),  constant (2::Int16))),
                        (Sm.tup2 (constant (3::Int32), constant (4::Int64)))),
               (Sm.tup2 (constant (5::Float), constant (6::Double))))

p13f :: Acc (Scalar ((Int8,Int16),(Int32,Int64),Int))
p13f = unit $ 
      Sm.tup3 ((Sm.tup2 (constant (1::Int8),  constant (2::Int16))),
               (Sm.tup2 (constant (3::Int32), constant (4::Int64))),
               (constant (5::Int)))

--  Unit (TArray 0 (TTuple [TTuple [TInt64,TInt32],TInt16,TInt8]))
--  ((((), Int8), Int16), Int32):
--  ((((), Int8), Int16), (((), Int32), Int64)):
--  Why is it not (((), (((), Int8), Int16)), (((), Int32), Int64)) ??
--  Why does it appear to follow a different convention for tuples of tuples?

--------------------------------------------------------------------------------
-- And test projection as well:

p14 = unit $ prj1_2 p13c_

p14b :: Acc (Scalar (Int8,Int16), Scalar Int32)
p14b = let (a,b) = untup2 p13c_ in
       lift (unit a, unit b)

p14c = unit $ prj1_3 p13b_
p14d = A.map prj1_3 p13b
-- Surface : TTuple [TTuple [TTuple [TTuple [],TInt8],TInt16],TInt32]
p14e = A.map prj1_2 p13c
-- Surface : TTuple [TTuple [TTuple [TTuple [],TInt8],TInt16],TInt32]

-- Project the second element from the right:
prj1_2 :: (Elt a, Elt b) => Sm.Exp (a, b) -> (Sm.Exp a)
prj1_2 e = Sm.Exp $ Tu.SuccTupIdx Tu.ZeroTupIdx `Sm.Prj` e

prj1_3 :: (Elt a, Elt b, Elt c) => Sm.Exp (a, b, c) -> (Sm.Exp b)
prj1_3 e = Sm.Exp $ Tu.SuccTupIdx Tu.ZeroTupIdx `Sm.Prj` e


tix0 :: Elt s => Tu.TupleIdx (t, s) s
tix0 = Tu.ZeroTupIdx
tix1 :: Elt s => Tu.TupleIdx ((t, s), s1) s
tix1 = Tu.SuccTupIdx tix0

untup2 :: (Elt a, Elt b) => Sm.Exp (a, b) -> (Sm.Exp a, Sm.Exp b)
untup2 e = (Sm.Exp $ Tu.SuccTupIdx Tu.ZeroTupIdx `Sm.Prj` e, 
            Sm.Exp $ Tu.ZeroTupIdx `Sm.Prj` e)

{-

untup3 :: (Elt a, Elt b, Elt c) => Exp (a, b, c) -> (Exp a, Exp b, Exp c)
untup3 e = (Exp $ SuccTupIdx (SuccTupIdx ZeroTupIdx) `Prj` e, 
            Exp $ SuccTupIdx ZeroTupIdx `Prj` e, 
            Exp $ ZeroTupIdx `Prj` e)
-}

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
        , testGroup "run p1a" (runBoth p1a)   -- fromIntegral
        , testGroup "run p1aa" (runBoth p1aa)
        , testGroup "run p1b" (runBoth p1b)
        , testGroup "run p1c" (runBoth p1c)
        , testGroup "run p1d" (runBoth p1d)
          
        , testGroup "run p2" (runBoth p2)
        , testGroup "run p2a" (runBoth p2a)          
        , testGroup "run p2b" (runBoth p2b) -- EIndexHeadDynamic
        , testGroup "run p2c" (runBoth p2c)
        , testGroup "run p2cc" (runBoth p2cc)          
        , testGroup "run p2d" (runBoth p2d)
        , testGroup "run p2e" (runBoth p2e)
        , testGroup "run p2f" (runBoth p2f)          
        , testGroup "run p2g" (runBoth p2g)    
        , testGroup "run p2h" (runBoth p2h)          
        
        , testGroup "run p3" (runBoth p3)  
        , testGroup "run p4" (runBoth p4)  
        , testGroup "run p4b" (runBoth p4b)  
        , testGroup "run p5" (runBoth p5)   
        , testGroup "run p6" (runBoth p6)    
        , testGroup "run p7" (runBoth p7)      
        , testGroup "run p8" (runBoth p8)
        , testGroup "run p9" (runBoth p9)
        , testGroup "run p9b" (runBoth p9b)
          
        , testGroup "run p10" (runBoth p10)          
        , testGroup "run p10b" (runBoth p10b)
        , testGroup "run p10c" (runBoth p10c)
        , testGroup "run p11" $ hUnitTestToTests $ I.run p11 ~=? run p11
        , testGroup "run p11b" $ hUnitTestToTests $ I.run p11b ~=? run p11b
        , testGroup "run p11c" $ hUnitTestToTests $ I.run p11c ~=? run p11c
        , testGroup "run p12" $ hUnitTestToTests $ I.run p12 ~=? run p12
          
        , testGroup "run p13" $ hUnitTestToTests $ I.run p13 ~=? run p13                  
        , testGroup "run p13b" $ hUnitTestToTests $ I.run p13b ~=? run p13b                   
        , testGroup "run p13c" $ hUnitTestToTests $ I.run p13c ~=? run p13c  
        , testGroup "run p13d" $ hUnitTestToTests $ I.run p13d ~=? run p13d   
        , testGroup "run p13e" $ hUnitTestToTests $ I.run p13e ~=? run p13e   
        , testGroup "run p13f" $ hUnitTestToTests $ I.run p13f ~=? run p13f    
        
        , testGroup "run p14" $ hUnitTestToTests $ I.run p14 ~=? run p14
        , testGroup "run p14b" $ hUnitTestToTests $ I.run p14b ~=? run p14b        
        , testGroup "run p14c" $ hUnitTestToTests $ I.run p14c ~=? run p14c        
        , testGroup "run p14d" $ hUnitTestToTests $ I.run p14d ~=? run p14d        
--        , testGroup "run p14e" $ hUnitTestToTests $ I.run p14e ~=? run p14e  -- Won't work until we fix tuple-type ambiguity.
        ]
 where
  runBoth p = (hUnitTestToTests$ Sug.toList (I.run p) ~=? Sug.toList (run p))

instance Eq a => Eq (Array sh a) where
  a1 == a2 = Sug.toList a1 == Sug.toList a2

-- main = print (I.run p8)
