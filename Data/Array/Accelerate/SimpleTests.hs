{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A battery of simple tests for any new SimpleAST-based  backend.

module Data.Array.Accelerate.SimpleTests 
   (testCompiler, testPartialCompiler, TestEntry,

    -- * ALL exported test programs in one list.
    allProgs, allProgsMap,

    -- * A breakdown of `allProgs`
    generateOnlyProgs, unitProgs, otherProgs,

    -- * An orthogonal breakdown of `allProgs`
    sliceProgs, noSliceProgs,

    -- * Individual tests:
    p1aa , p1ab , p1ac ,
    p2aa, p2a , p2f , p4 , p4b , p5 , p0 , p1 , p1b , p1c , p1d , p2 , p2b , p2c , p2cc , p2d , p2e , p2g , p2h , p3 , p2b , p6 , p8 , p9 , p9b , p10 , p10b , p10c , p11 , p11b , p11c , p12 , p13 , p13b , p13c , p13d , p13e , p13f , p14 , p14b , p14c , p14d , p14e , p16a , p16b , p16c , p16d
   )
   where 

import           Data.Array.Accelerate.SimpleConverter (convertToSimpleProg, unpackArray, Phantom)
import qualified Data.Array.Accelerate.SimpleAST    as S
import qualified Data.Array.Accelerate.Smart       as Sm
import qualified Data.Array.Accelerate.Tuple       as Tu
import qualified Data.Array.Accelerate.Array.Sugar as Sug

import Data.Array.Accelerate as A 
import Data.Array.Accelerate.Interpreter (run)
import Data.Int
import Data.List       (intersperse)
import Data.List.Split (chunksOf)
--import Control.DeepSeq (deepseq)
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Prelude  as P
import Prelude hiding (zipWith,replicate,map)
import Test.Framework (testGroup, defaultMain, Test)
-- import qualified Test.Framework as TF
import Test.Framework.Providers.HUnit
import Test.HUnit      ((~=?), (~?))
import Text.PrettyPrint.GenericPretty (doc)

-- | A tuple containing name, AST, and the printed result produced by evaluating under
--   the reference Accelerate interpreter, and THEN flattened/printed as an S.AccArray.
type TestEntry = (String, S.Prog (), String)

-- | ALL test programs.
allProgs :: [TestEntry]
allProgs = generateOnlyProgs ++ unitProgs ++ otherProgs

-- | `allProgs` organized by name for easy lookup.
allProgsMap :: M.Map String TestEntry
allProgsMap = M.fromList $ P.map fn allProgs
 where
   fn x@(name,_,_) = (name,x)
  
-- | These tests only use 
generateOnlyProgs :: [TestEntry]
generateOnlyProgs = [ 
  go "p1aa" p1aa,
  -- go "p1a" p1a,
  go "p1ab" p1ab,
  go "p1ac" p1ac
  ]

-- | Programs that use Unit.
unitProgs :: [TestEntry]
unitProgs = [
  go "p2a" p2a, go "p2f" p2f,
  go "p4" p4, go "p4b" p4,
  go "p5" p5
 ]

-- | Every test program that does not fall into the above categories.
otherProgs :: [TestEntry]
otherProgs = 
  [
  go "p0" p0,                
  go "p1" p1, 
  go "p1b" p1b, go "p1c" p1c, go "p1d" p1d,
  go "p2" p2, go "p2aa" p2aa, go "p2b" p2b, go "p2c" p2c, go "p2cc" p2cc, 
  go "p2d" p2d, go "p2e" p2e, go "p2g" p2g, go "p2h" p2h,  
  go "p3" p3, 
  go "p2b" p2b,
  go "p6" p6, 
--  go "p7" p7, 
  go "p8" p8, 
  go "p9" p9, go "p9b" p9b,
  go "p10" p10, go "p10b" p10b, go "p10c" p10c, 
  go "p11" p11, go "p11b" p11b, go "p11c" p11c,
  go "p12" p12, 
  go "p13" p13, go "p13b" p13b, go "p13c" p13c, go "p13d" p13d, go "p13e" p13e, go "p13f" p13f,
  go "p14" p14, go "p14b" p14b, 
  go "p14c" p14c, go "p14d" p14d, go "p14e" p14e,

  go "p16a" p16a, go "p16b" p16b, go "p16c" p16c, go "p16d" p16d
  ]

go :: forall a . (Arrays a) => String -> Acc a -> TestEntry
go name p =
  let arr = run p -- Run through the official Accelerate interpreter.
      -- Then we unpack the results into our plainer format. 
      (repr :: Sug.ArrRepr a) = Sug.fromArr arr  -- Array typing nonsense.
      (_ty, arr2, _phantom :: Phantom a) = unpackArray repr
      payloads = S.arrPayloads arr2
      -- Compare the *flat* list of payloads only for now; we record the printed payload:
  in (name, convertToSimpleProg p, show payloads) 
       
----------------------------------------------------------------------------------------------------
-- Extra categories that are orthogonal to the above:

-- | All tests using a notion of /Slices/, namely Replicate and Index.
sliceProgs :: [TestEntry]
sliceProgs = [
  go "p2f" p2f,
  go "p2" p2, go "p2b" p2b, go "p2cc" p2cc, 
  go "p2d" p2d, go "p2e" p2e, go "p2h" p2h,
  go "p3" p3,
  go "p9" p9, go "p9b" p9b,
  go "p10" p10, go "p10b" p10b, go "p10c" p10c
  ]

noSliceProgs :: [TestEntry]
noSliceProgs = Set.toList$ 
  Set.difference (Set.fromList allProgs)
                 (Set.fromList sliceProgs)

----------------------------------------------------------------------------------------------------

-- | Test a complete compiler backend.  Construct a list of
-- `test-framework` tests for a backend.
testCompiler :: (String -> S.Prog () -> [S.AccArray]) -> [TestEntry] -> [Test]
testCompiler eval progs = P.map mk (P.zip [0..] progs)
 where 
   mk (i, (name, prg, ans)) = 
     let payloads = concatMap S.arrPayloads (eval name prg) in 
     -- let [t] = hUnitTestToTests $ (show (eval prg)) ~=? ans in
     -- testCase ("run test "++show i) t 
     testGroup ("run test "++show i++" "++name) $
     hUnitTestToTests $ 
     ans ~=? (show payloads) -- EXPECTED goes on the left.

-- | Test a compiler which does some passes but doesn't compute a
-- final answer.  This requires an oracle function to determine
-- whether the output is good.
testPartialCompiler :: Show a => (S.Prog () -> a -> Bool) -> (String -> S.Prog () -> a) -> [TestEntry] -> [Test]
testPartialCompiler oracle eval tests = P.map mk (P.zip [0..] tests)
  where
   mk (i, (name, prg, ans)) =
     testGroup ("run test "++show i++" "++name) $
     hUnitTestToTests $ 
     (True ~=?) $ 
      let evaled = eval name prg in
      seq (forceEval evaled) $
      oracle prg evaled

   -- HACK: We don't want to require NFData (yet).  So we just print to force Eval:
   forceEval prog = length (show prog)
        
----------------------------------------------------------------------------------------------------

p0 :: Acc (Array DIM2 Int64)
p0 = use $ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Int64]
t0 = convertToSimpleProg p0

-- | Sharing recovery will create a Let here:
p1 :: Acc (Scalar Int)
p1 = fold (+) 0 (zipWith (*) p1aa p1aa)
t1 = convertToSimpleProg p1

-- | Just generate 
p1aa :: Acc (Vector Int)
p1aa = generate (constant (Z :. (10::Int)))
       (unindex1)

p1ba :: Acc (Vector Int32)
p1ba = generate (constant (Z :. (10::Int)))
       (A.fromIntegral . unindex1)


-- | Also exercise fromIntegral:
p1a :: Acc (Vector Float)
p1a = generate (constant (Z :. (10::Int))) (A.fromIntegral . unindex1_int)

p1ab :: Acc (Vector Float)
p1ab = generate (constant (Z :. (10::Int)))
                (\ ind -> A.fromIntegral (unindex1_int ind) + 3.3)

p1ac :: Acc (Scalar Double)
p1ac = generate (constant Z)
                (\ _ind -> 4.4 / 2.0)


index1_int   a = (unindex1 (a :: Exp DIM1)) :: Exp Int
unindex1_int a = (unindex1 a) :: Exp Int


-- | And again with a 2D array:
p1b :: Acc (Vector Float)
p1b = let xs = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
      in  fold (+) 0 xs
t1b = convertToSimpleProg p1b


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

-- A 2D version of previous:
p2aa :: Acc (Array DIM2 Int32)
p2aa = let xs = replicate (constant (Z :. (4::Int) :. (3::Int))) (unit 40)
       in map (+ 10) xs


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


-- There isn't really much support for non-Int indices... I think we
-- should force them to be Ints:
--     No instance for (Shape (Z :. Word32))
-- p2i :: Acc (Array (Z :. Word32) Int8)
-- p2i = replicate (constant (Z :. (4::Word32))) (unit 44)
-- p2i = use $ fromList (Z :. (4::Word32)) [1..4]

--------------------------------------------------------------------------------

p3 :: Acc (Array DIM3 Int32)
p3 = let arr = generate  (constant (Z :. (5::Int))) (\_ -> 33)
         xs  = replicate (constant$ Z :. (2::Int) :. All :. (3::Int)) arr
     in xs 
t3 = convertToSimpleProg p3

-- Test 4, a program that creates an IndexScalar:
p4 :: Acc (Scalar Int64)
p4 = let arr = generate (constant (Z :. (5::Int))) (\_ -> 33) in
     unit $ arr ! (index1 (2::Exp Int))
        -- (Lang.constant (Z :. (3::Int)))  
t4 = convertToSimpleProg p4         

p4b :: Acc (Scalar Int64)
p4b = let arr = generate (constant (Z :. (3::Int) :. (3::Int))) (\_ -> 33) 
              :: Acc (Array DIM2 Int64)
      in
     unit $ arr ! (index2 (1::Exp Int) (2::Exp Int))
t4b = convertToSimpleProg p4b


-- This one generates EIndex. It creates an array containing a slice descriptor.
p5 :: Acc (Scalar (((Z :. All) :. Int) :. All))
p5 = unit$ lift $ Z :. All :. (2::Int) :. All
t5 = convertToSimpleProg p5

-- This one generates ETupProjectFromRight:
p6 :: Acc (Vector Float)
p6 = map go (use xs)
  where
    xs :: Vector (Float, Float)
    xs = fromList sh [(1,10),(2,20)]
    sh = Z :. (2::Int)
    go x = let (a,b) = unlift x   in a*b
t6 = convertToSimpleProg p6

-- | Transpose a matrix.
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
p12 = let arr = generate (constant (Z :. (5::Int))) unindex1_int in 
      cond (arr A.! (index1 (2::Exp Int)) >* 2)
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

-- Hmm [2012.06.27] 
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

p15 :: Acc (Vector Int)
p15 = A.filter (\_ -> constant True) (generate (constant$ Z :. 10) (\_ -> 40))


--------------------------------------------------------------------------------
-- Fusion tests:

p16a :: Acc (Vector Int)
p16a = map (*2) $ 
       map (+1) p1aa

-- This one triggers identical Zipwith branches turning it into a Map.
p16b :: Acc (Vector Int)
p16b = map (*2) $ zipWith (+) p1aa p1aa


-- This one can't eliminate the zipwith, but the Map will fuse on the other side.
-- Also, the two arms are different sizes, stressing the "intersection" semantics.
p16c :: Acc (Vector Int)
p16c = map (*2) $ zipWith (+) p1aa
          (generate (constant (Z :. (5::Int))) (unindex1))

-- This one can't fuse map->generate because of the double-use of one
-- generate, but it CAN fuse map into downstream zipwith.  And THEN
-- that opens up the possibility of converting the zipWith to a Map
-- and finally fusing in the generate (resulting in a single Generate).
p16d :: Acc (Vector Int)
p16d = zipWith (+) p1aa p16a
-- This one presently prints no less than FIVE victory messages.

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
         maxpad = P.maximum$ P.map length ls

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
         maxpad = P.maximum$ P.map length ls
         rowls = chunksOf cols ls

--------------------------------------------------------------------------------
         
