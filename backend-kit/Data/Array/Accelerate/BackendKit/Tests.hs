{-# LANGUAGE TypeOperators, NamedFieldPuns, ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}

-- | A battery of simple tests for any new SimpleAST-based  backend.

module Data.Array.Accelerate.BackendKit.Tests
   (testCompiler, testPartialCompiler, TestEntry(..), AccProg(..), makeTestEntry, 

    -- * ALL exported test programs in one list.
    allProgs, allProgsMap,

    -- * A breakdown of `allProgs`
    generateOnlyProgs, unitProgs, otherProgs,

    -- * An orthogonal breakdown of `allProgs`
    sliceProgs, noSliceProgs,

    -- * Individual tests:
    p1a, p1aa, p1ab, p1ac, p1ba,
    p2aa, p2a, p2ab, p2f, p4, p4b, p4c, p5, p0, p1, p1b, p1bb, p1c, p1d,
    p2, p2b, p2bb, p2c, p2cc, p2cd, p2ce, p2d, p2e, p2g, p2h, p2i, 
    p3,
    p6, p6b,
    p8, p9a, p9b, p9c, 
    p10, p10b, p10c, p10d, p10e, p10f, p10g, p10h, p10i, 
    p11, p11b, p11c,
    {-p12,-} p12b, p12c, p12d, p12e,
    p13, p13a, p13b, p13c, p13d, p13e, p13f, p13g, p13g2, p13h, p13i, p13j, p13k, 
    p14, p14b, p14c, p14d, p14e, 
    p16a, p16b, p16c, p16d, p16e, p17a, p17b,
    p18a, p18b, p18c, p18d, p18e, p18f,

    p20a, p20b, p20c, 

    -- Scan tests
    p30, p31, p32, p33,
    p40a, p40b, p41a, p41b, 

    -- Iteration
    p50a, p50b, p50c,
    
    p60a, p60b, p60c, p60d, p60e, p60f, p60g, p60h, p60i,
    
    -- Naughty tuples 
    p70, p70a,     

    -- Use Tuples 
    p80, p80a, p80b,  p80c, p80d, p80e,

    p90, p90a, p90b, p90c,

    p91, p91a, p91b ,p91c ,p91d,

    p92, p92a, 
 
    -- * Reexports to make life easier:
    doc, convertToSimpleProg,

    -- Temp:
    p2b_slc, p2b_test
   )
   where 

import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0,phase1, phase2, unpackArray, Phantom)
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as I
import qualified Data.Array.Accelerate.Smart       as Sm
import qualified Data.Array.Accelerate.Tuple       as Tu
import qualified Data.Array.Accelerate.Array.Sugar as Sug

import Data.Array.Accelerate as A hiding ((++)) 
import Data.Array.Accelerate.Interpreter (run)
import Data.Int
import Data.List (intersperse)
import qualified Data.List as L
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
import Text.PrettyPrint.GenericPretty (doc, Out(doc,docPrec), Generic)
import Text.PrettyPrint.HughesPJ (text)

-- | A tuple containing name, AST, and the printed result produced by evaluating under
--   the reference Accelerate interpreter, and THEN flattened/printed as an S.AccArray.
-- 
--   The TestEntry also provides access to the original Accelerate
--   program, but it is trickier to consume.
data TestEntry = TestEntry { name :: String  -- ^ Name of this particular test. 
                           , simpleProg :: S.Prog () -- ^ Converted SimpleAcc AST
                           , simpleResult :: String  -- ^ Result printed as a simplified, flattened list of payloads, [ArrayPayload].
                           , interpResult :: String  -- ^ Result as printed by Accelerate.Interpreter
                           , origProg :: AccProg     -- ^ Original, fully typed Accelerate program 
                           }
 deriving (Show, Ord, Eq, Generic)

instance Out TestEntry
instance Out AccProg where docPrec _ = text . show; doc = docPrec 0

-- | A simple way to encapsulate an Accelerate program of an arbitrary type.
data AccProg = forall a . (Arrays a, Show a) => AccProg (Acc a)

instance Show AccProg where
  show (AccProg acc) = show acc

instance Ord AccProg where
  -- HACK: Using printed representation:
  compare (AccProg a) (AccProg b) = compare (show a) (show b)
  
instance Eq AccProg where
  -- HACK: Using printed representation:
  AccProg a == AccProg b = show a == show b
  
-- | ALL test programs.
allProgs :: [TestEntry]
allProgs = generateOnlyProgs ++ unitProgs ++ otherProgs

-- | `allProgs` organized by name for easy lookup.
allProgsMap :: M.Map String TestEntry
allProgsMap = M.fromList $ P.map fn allProgs
 where
   fn x@TestEntry{name} = (name,x)
  
-- | These tests only use 
generateOnlyProgs :: [TestEntry]
generateOnlyProgs = [ 
  go "p1a"  p1a,  
  go "p1aa" p1aa,
  go "p1ba" p1ba,
  -- go "p1a" p1a,
  go "p1ab" p1ab,
  go "p1ac" p1ac
  ]

-- | Programs that use Unit.
unitProgs :: [TestEntry]
unitProgs = [
  go "p2a" p2a, go "p2ab" p2ab, go "p2f" p2f,
  go "p4" p4, go "p4b" p4b, go "p4c" p4c,
  go "p5" p5
 ]

-- | Every test program that does not fall into the above categories.
otherProgs :: [TestEntry]
otherProgs = 
  [
  go "p0" p0,                
  go "p1" p1, 
  go "p1b" p1b,  go "p1bb" p1bb,
  go "p1c" p1c, go "p1d" p1d,
  go "p2" p2, go "p2aa" p2aa, go "p2b" p2b, go "p2bb" p2bb,
  go "p2c" p2c, go "p2cc" p2cc, go "p2cd" p2cd, go "p2ce" p2ce,
  go "p2d" p2d, go "p2e" p2e, go "p2g" p2g, go "p2h" p2h,  go "p2i" p2i,
  go "p3" p3, 
  go "p6" p6,  go "p6b" p6b, 
  go "p7" p7, 
  go "p8" p8, 
  go "p9a" p9a, go "p9b" p9b, go "p9c" p9c,
  go "p10" p10, go "p10b" p10b, go "p10c" p10c, go "p10d" p10d, go "p10e" p10e, go "p10f" p10f, 
  go "p10g" p10g, go "p10h" p10h, go "p10i" p10i, 
  go "p11" p11, go "p11b" p11b, go "p11c" p11c,
  -- go "p12" p12,  -- [2014.02.20] Temporarily disabled.  This one is nondeterministic (issue #8).  Returning to it later.
  go "p12b" p12b, go "p12c" p12c, go "p12d" p12d, go "p12e" p12e, 
  go "p13" p13, go "p13a" p13a, go "p13b" p13b, go "p13c" p13c, go "p13d" p13d, go "p13e" p13e, go "p13f" p13f,
  go "p13g" p13g, go "p13g2" p13g2, go "p13h" p13h, go "p13i" p13i, go "p13j" p13j, go "p13k" p13k,
  go "p14" p14, go "p14b" p14b, 
  go "p14c" p14c, go "p14d" p14d, go "p14e" p14e,

  go "p16a" p16a, go "p16b" p16b, go "p16c" p16c, go "p16d" p16d, go "p16e" p16e,
  go "p17a" p17a, go "p17b" p17b,
  go "p18a" p18a, go "p18b" p18b, go "p18c" p18c, go "p18d" p18d, go "p18e" p18e, go "p18f" p18f,

  go "p20a" p20a, go "p20b" p20b, go "p20c" p20c,

  -- Scan test                                   
  go "p30" p30, go "p31" p31, go "p32" p32, go "p33" p33,
  go "p40a" p40a, go "p40b" p40b, go "p41a" p41a, go "p41b" p41b,

  -- Iteration
  go "p50a" p50a,
  go "p50b" p50b,
  go "p50c" p50c,

  -- Tuple experimentation 
  go "p60a" p60a, go "p60b" p60b,   go "p60c" p60c, go "p60d" p60d, 
  go "p60e" p60e, go "p60f" p60f, go "p60g" p60g, go "p60h" p60h, go "p60i" p60i,
  go "p70" p70,   go "p70a" p70a ,

  -- Use tuples 
  go "p80" p80 , go "p80a" p80a , go "p80b" p80b , go "p80c" p80c , go "p80d" p80d , go "p80e" p80e ,

  -- More ~nasty~ tuples
  go "p90" p90 , go "p90a" p90a , go "p90b" p90b , go "p90c" p90c ,

  go "p91" p91 , go "p91a" p91a , go "p91b" p91b , go "p91c" p91c , go "p91d" p91d

  --,
  -- These two send the backend-kit into infinite loop.  
  -- go "p92" p92,  go "p92a" p92a
  ]

makeTestEntry :: forall a . (Show a, Arrays a) => String -> Acc a -> TestEntry
makeTestEntry = go

-- | The function that builds TestEntries.
go :: forall a . (Show a, Arrays a) => String -> Acc a -> TestEntry
go name p =
  let arr = run p -- Run through the official Accelerate interpreter.
      -- Then we unpack the results into our plainer format. 
--      (repr :: Sug.ArrRepr a) = Sug.fromArr arr  -- Array typing nonsense.
--      (_ty, arr2, _phantom :: Phantom a) = unpackArray repr
      [arr2]    = unpackArray arr
      payloads  = S.arrPayloads arr2
      -- Compare the *flat* list of payloads only for now; we record the printed payload:
  in TestEntry { name
               , simpleProg = convertToSimpleProg p
               , simpleResult = show payloads -- accArrays
               , interpResult = show arr
               , origProg = AccProg p }
       
----------------------------------------------------------------------------------------------------
-- Extra categories that are orthogonal to the above:

-- | All tests using a notion of /Slices/, namely Replicate and Index.
sliceProgs :: [TestEntry]
sliceProgs = [
  go "p2f" p2f,
  go "p2" p2, go "p2b" p2b, go "p2bb" p2bb, go "p2cc" p2cc, go "p2cd" p2cd, 
  go "p2d" p2d, go "p2e" p2e, go "p2h" p2h, go "p2i" p2i,
  go "p3" p3,
  go "p9a" p9a, go "p9b" p9b, 
  go "p10" p10, go "p10b" p10b, go "p10c" p10c
  ]

noSliceProgs :: [TestEntry]
noSliceProgs = Set.toList$ 
  Set.difference (Set.fromList allProgs)
                 (Set.fromList sliceProgs)

----------------------------------------------------------------------------------------------------

-- | Test a complete compiler backend starting from the point after
-- conversion to the simplified AST.  Construct a list of
-- `test-framework` tests for a backend.
testCompiler :: (String -> S.Prog () -> [S.AccArray]) -> [TestEntry] -> [Test]
testCompiler eval progs = P.map mk (P.zip [(0::Int)..] progs)
 where 
   mk (i, TestEntry {name, simpleProg, simpleResult}) = 
     let payloads = concatMap S.arrPayloads (eval name simpleProg) in 
     testGroup ("run test "++show i++" "++name) $
     hUnitTestToTests $ 
     simpleResult ~=? (show payloads) -- EXPECTED goes on the left.

-- | Test a compiler which does some passes but doesn't compute a
-- final answer.  This requires an oracle function to determine
-- whether the output is good.
testPartialCompiler :: Show a => (S.Prog () -> a -> Bool) -> (String -> S.Prog () -> a) -> [TestEntry] -> [Test]
testPartialCompiler oracle eval tests = P.map mk (P.zip [0..] tests)
  where
   mk (i, TestEntry { name, simpleProg } ) =
     testGroup ("run test "++show i++" "++name) $
     hUnitTestToTests $ 
     (True ~=?) $ 
      let evaled = eval name simpleProg in
      seq (forceEval evaled) $
      oracle simpleProg evaled

   -- HACK: We don't want to require NFData (yet).  So we just print to force Eval:
   forceEval prog = P.length (show prog)
        
----------------------------------------------------------------------------------------------------

p0 :: Acc (Array DIM2 Int64)
-- The innermost (fastest changing) dimension is size 5:
p0 = use $ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Int64]
r0 = I.run p0

-- | Sharing recovery will create a Let here:
p1 :: Acc (Scalar Int)
p1 = fold (+) 0 (zipWith (*) p1aa p1aa)

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


index1_int :: Exp Int -> Exp DIM1 
index1_int = index1

unindex1_int :: Exp DIM1 -> Exp Int
unindex1_int  = unindex1 


-- | And again with a 2D array:
p1b :: Acc (Vector Float)
p1b = let xs = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
      in  fold (*) 1 xs

-- | Same 2D->1D fold test but with generate instead of use...
p1bb :: Acc (Vector Float)
p1bb = fold (+) 0 p17b


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

-- A 2D version of previous:
p2aa :: Acc (Array DIM2 Int32)
p2aa = let xs = replicate (constant (Z :. (4::Int) :. (3::Int))) (unit 40)
       in map (+ 10) xs


p2a :: Acc (Scalar Word)
p2a = unit 40

-- | Shapes are valid constants also.
p2ab :: Acc (Scalar (Z :. Int))
p2ab = unit (constant (Z :. (4::Int)))


-- This is an example of the weird encoding we get where slice expressions with All's
-- on the outer most dimensions don't have a representation (unit) of those All's.
p2b :: Acc (Array DIM2 Int)
p2b = let arr = generate (constant (Z :. (5::Int))) unindex1
--      in replicate (constant$ Z :. (4::Int) :. All) arr
      in replicate (constant$ Z :. All :. (4::Int)) arr
          -- 1st generates: Array (Z :. 4 :. 5) [0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4]
          -- 2nd generates: Array (Z :. 5 :. 4) [0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4]

p2b_slc = (constant$ Z :. All :. (4::Int))


p2b_test :: Acc (Array DIM2 Int)
p2b_test = let arr = generate (constant (Z :. (5::Int))) unindex1
      in replicate p2b_slc arr

-- A replicate-of-replicate with a 3D result:
p2bb :: Acc (Array DIM3 Int)
-- Array (Z :. 5 :. 3 :. 4) 
p2bb = replicate (constant$ Z :. All :. (3::Int) :. All) p2b


-- | A 2D array with some tuple operations:
p2c :: Acc (Array DIM2 Int)
p2c = generate (constant (Z :. (3::Int) :. (3::Int)))
               (\e -> let (r,c) = unlift$ unindex2 e in 3 * r + c)
-- Output: Array (Z :. 3 :. 3) [0,1,2,3,4,5,6,7,8]

-- | Expand 2D -> 3D
p2cc :: Acc (Array DIM3 Int)
p2cc = replicate (constant$ Z :. (2::Int) :. All :. All) p2c
-- Output: Array (Z :. 2 :. 3 :. 3) [0,1,2,3,4,5,6,7,8,0,1,2,3,4,5,6,7,8]

-- | Dynamic size based on conditional.
p2cd :: Acc (Array DIM3 Int)
p2cd = replicate
       (constant True ?
        (constant$ Z :. (2::Int) :. All :. All,
         constant$ Z :. (7::Int) :. All :. All))
       p2c

p2ce :: Acc (Array DIM3 Int)
p2ce = replicate
       (constant$ Z :. (7::Int) :. All :. (2::Int))
       (generate (index1 3) unindex1)


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

-- | Same as p2d exept without an array-of-tuples
p2i :: Acc (Array DIM4 Int)
p2i = let arr = generate (constant (Z :. (3::Int) :. (3::Int)))
                         (\ ix ->
                           let (a,b) = untup2 (unindex2 ix) in
                           a + b
                         )
      in replicate (constant$ Z :. All :. (2::Int) :. All :. (2::Int)) arr



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

-- Test 4, a program that creates an IndexScalar:
p4 :: Acc (Scalar Int64)
p4 = let arr = generate (constant (Z :. (5::Int))) (\_ -> 33) in
     unit $ arr ! (index1 (2::Exp Int))
        -- (Lang.constant (Z :. (3::Int)))  

-- Ditto with more dimensions:
p4b :: Acc (Scalar Int64)
p4b = let arr = generate (constant (Z :. (3::Int) :. (3::Int))) (\_ -> 33) 
              :: Acc (Array DIM2 Int64)
      in
     unit $ arr ! (index2 (1::Exp Int) (2::Exp Int))

-- This one is expensive, to resist inlineCheap:
p4c :: Acc (Scalar Int)
p4c = let arr = generate (constant (Z :. (5::Int)))
                  (\ix -> (foldl1 (+) (P.replicate 10 (unindex1_int ix)))) in
     unit $ arr ! (index1 (2::Exp Int))
        -- (Lang.constant (Z :. (3::Int)))  



-- This one generates EIndex. It creates an array containing a slice descriptor.
p5 :: Acc (Scalar (((Z :. All) :. Int) :. All))
p5 = unit$ lift $ Z :. All :. (2::Int) :. All

------------------------------------------------------------
-- Scalar tuples and projection:
------------------------------------------------------------

-- This one generates ETupProjectFromRight:
-- (But it requires an array-of-tuples internally:)
p6 :: Acc (Vector Float)
p6 = map go (use xs)
  where
    xs :: Vector (Float, Float)
    xs = fromList sh [(1,10),(2,20)]
    sh = Z :. (2::Int)
    go x = let (a,b) = unlift x   in a*b

-- Use a simple test that doesn't have any tuples-of-arrays, but DOES have a scalar level tuple internally.
p6b :: Acc (Scalar Int)
p6b = unit y
  where
    y = a + b
    (a,b) = unlift x    
    x :: Exp (Int,Int)
    x = lift (2::Int, 3::Int)

------------------------------------------------------------
-- | Transpose a matrix.
------------------------------------------------------------
    
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
-- TODO -- still need to generate an IndexCons node.

----------------------------------------

-- This shows an odd difference in staging:
p8 :: Acc (Scalar Float)
p8 = unit$ pi + (constant pi :: Exp Float) *
           negate (negate (abs (signum pi)))

-- Prim arguments don't need to directly be tuple expressions:
-- unit ((+) (let x0 = pi in (x0, 3.1415927 * x0)))


------------------------------------------------------------
-- P9: Experimenting with Tuples:
------------------------------------------------------------

-- A map with a tuple return type:
p9a :: Acc (Vector (Int32,Int32))
p9a = let xs = replicate (constant (Z :. (4::Int))) (unit 40)
      in map (\ x -> lift (x+10, x*10)) xs

-- How about tuples coming in and going out:
p9b :: Acc (Vector (Int32,Int32,Int32))
p9b = map (\ e ->  
                  let (x,y) = unlift e in 
--                  (x::Exp Int32) + (y::Exp Int32)
                  lift (x::Exp Int32, y::Exp Int32, x+y)
          )
          p9a
 
-- A generate of an array of tuples
p9c :: Acc (Vector (Float,Int))
p9c = generate (index1 10) $ \ind -> 
        let i = unindex1_int ind in 
        lift (A.fromIntegral i + 30.3, i + 100)

-- Take a contiguous section out of a large tuple:
p9d :: Acc (Scalar (Int,Int,Int))
p9d = unit$
  let x :: (Int,Int,Int,Int,Int)
      x = (1,2,3,4,5)
      t :: Exp (Int,Int,Int,Int,Int)
      t = lift x
      (a,b,c,d,e) :: (Exp Int,Exp Int,Exp Int,Exp Int,Exp Int) = unlift t
      v :: Exp (Int,Int,Int)
      v = lift (b,c,d)
  in v

-- Now a large nested tuple:


-- p9e :: Acc (Scalar (Int,Int,Int))
p9e :: Acc (Scalar (Int,(Int,Int,Int)))
p9e = unit$
  let x :: (Int,(Int,(Int,Int,Int)),Float)
      x = (1,(2,(3,4,5)),6)
      t :: Exp (Int,(Int,(Int,Int,Int)),Float)
      t = lift x

      u :: (Exp Int,Exp (Int,(Int,Int,Int)),Exp Float)
--      u :: (Exp Int,(Exp Int,(Exp Int,Exp Int,Exp Int)),Exp Float)
      u = unlift t
      (a,mid,f) = u      
--      (a,(b,(c,d,e)),f) :: (Exp Int,(Exp Int,(Exp Int,Exp Int,Exp Int)),Exp Float) = unlift t
      -- v :: Exp (Int,Int,Int)
      -- v = lift (b,c,d)
  in mid


--------------------------------------------------------------------------------
-- How do we create IndexAny in the AST?

-- repN :: Int -> Array sh e -> Acc (Array (sh:.Int) e)
-- repN n a = replicate (Any :. n) a

repN :: (Shape sh, Elt e) => Int -> Acc (Array sh e) -> Acc (Array (sh:.Int) e)
repN n a = replicate (constant$ Any :. n) a

p10 :: Acc (Array DIM1 Float)
p10 = repN 3 (unit 40.4)

-- A 4x3 matrix, shape (Z :. 3 :. 4):
p10b :: Acc (Array DIM2 Float)
p10b = repN 4 p10

p10c :: Acc (Array DIM1 Float)
p10c = replicate (constant$ Any :. (3::Int)) (unit 4.4)

-- p10d :: Acc (Array DIM2 Float)
p10d :: Acc (Scalar Float)
p10d = slice p10b (constant (Z :. (2::Int) :. (2::Int)))

-- Project a four-element row:
p10e :: Acc (Vector Float)
p10e = slice p10b (constant (Z :. (2::Int) :. All))

-- Project a three-element column:
p10f :: Acc (Vector Float)
p10f = slice p10b (constant (Z :. All :. (2::Int)))

-- A 0D slice of 1D vector:
p10g :: Acc (Scalar Float)
p10g = slice p10 (index1_int 1)

-- A 0D slice of a 1D vec of unknown size:
p10h :: Acc (Scalar Int)
p10h = slice p18a (index1_int 1)

-- A pointless 1D slice of 1D vector:
p10i :: Acc (Vector Int)
p10i = slice p18a (constant$ Z:.All)



------------------------------------------------------------
-- How about tuples of arrays?
------------------------------------------------------------

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


------------------------------------------------------------
-- P12: Conditionals

-- | Array level conditional:
{-p12 :: Acc (Scalar Word32, Scalar Float)
p12 = let arr = generate (constant (Z :. (5::Int))) unindex1_int in 
      cond (arr A.! (index1 (2::Exp Int)) >* 2)
           (lift (unit 10, unit 20.0))
           (lift (unit 40, unit 30.0))-}

-- | Scalar level conditional
p12b :: Acc (Scalar Int)
p12b = unit (constant True ? (11, 22))

-- | Scalar conditional in more complex context:
p12c :: Acc (Scalar Int)
p12c = unit (33 + (constant True ? (11, 22)))


-- | Scalar conditional with a more complex branch.
p12d :: Acc (Scalar Int)
p12d = unit (33 + (constant True ? (11, let x = 22 in x * x * x)))

-- | Scalar conditional with a tuple return type:
p12e :: Acc (Scalar Int)
p12e = unit $
  let tup :: Exp (Int,Int)
      tup   = constant True ? (lift (11::Int, 22::Int),
                               lift (100::Int,200::Int))
      (a,b) = unlift tup :: (Exp Int, Exp Int)
  in a + 33



--------------------------------------------------------------------------------
-- Scalar tuples: Let's test tuple simple-AST conversion:
---------------------------------------------------------

p13 :: Acc (Scalar ((Int8,Int16),(Int32,Int64)))
p13 = unit $ 
      Sm.tup2 ((Sm.tup2 (constant (1::Int8),  constant (2::Int16))),
               (Sm.tup2 (constant (3::Int32), constant (4::Int64))))

p13a :: Acc (Scalar (Int8,(Int16,Int32)))
p13a = unit p13a_
p13a_ = Sm.tup2 (constant (1::Int8),
                 (Sm.tup2 (constant (5::Int16), constant (2::Int32))))


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

p13g :: Acc (Scalar Z)
p13g = unit $ constant Z

p13g2 :: Acc (Vector Z)
p13g2 = generate (constant (Z :. (10::Int))) (\_ -> constant Z)

p13h :: Acc (Scalar (Z :. Int))
p13h = unit $ constant (Z :. 3)

p13i :: Acc (Scalar (Z :. Int :. Int))
p13i = unit $ constant (Z :. 3 :. 4)

p13j :: Acc (Scalar (Z :. All :. Int))
p13j = unit $ constant (Z :. All :. 4)

p13k :: Acc (Scalar (Z :. Int :. All))
p13k = unit $ constant (Z :. 3 :. All)

--------------------------------------------------------------------------------
-- And test projection as well:

p14 :: Acc (Scalar (Int8,Int16))
p14 = unit $ prj1_2 p13c_

-- Hmm [2012.06.27] 
p14b :: Acc (Scalar (Int8,Int16), Scalar Int32)
p14b = let (a,b) = untup2 p13c_ in
       lift (unit a, unit b)

p14c :: Acc (Scalar Int16)
p14c = unit $ prj1_3 p13b_

p14d :: Acc (Scalar Int16)
p14d = A.map prj1_3 p13b
-- Surface : TTuple [TTuple [TTuple [TTuple [],TInt8],TInt16],TInt32]

-- Fails when DEBUG > 0 
-- success otherwise 
p14e :: Acc (Scalar (Int8,Int16))
p14e = A.map prj1_2 p13c
-- Surface : TTuple [TTuple [TTuple [TTuple [],TInt8],TInt16],TInt32]

-- Project the second element from the right:
prj1_2 :: (Elt a, Elt b) => Sm.Exp (a, b) -> (Sm.Exp a)
prj1_2 e = Sm.Exp $ Tu.SuccTupIdx Tu.ZeroTupIdx `Sm.Prj` e

prj1_3 :: (Elt a, Elt b, Elt c) => Sm.Exp (a, b, c) -> (Sm.Exp b)
prj1_3 e = Sm.Exp $ Tu.SuccTupIdx Tu.ZeroTupIdx `Sm.Prj` e

prj2_4 :: (Elt a, Elt b, Elt c, Elt d) => Exp (a, (b, c), d) -> (Exp (b,c))
prj2_4 e = 
  -- Sm.Exp $ Tu.SuccTupIdx Tu.ZeroTupIdx `Sm.Prj` e
  undefined

tix0 :: Elt s => Tu.TupleIdx (t, s) s
tix0 = Tu.ZeroTupIdx
tix1 :: Elt s => Tu.TupleIdx ((t, s), s1) s
tix1 = Tu.SuccTupIdx tix0

-- Here we manually construct some of the AST we want:
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

-- | Trying filter:
p15 :: Acc (Vector Int)
p15 = A.filter (\_ -> constant True) (generate (constant$ Z :. 10) (\_ -> 40))


--------------------------------------------------------------------------------
-- Fusion tests:

p16a :: Acc (Vector Int)
p16a = map (*2) $ 
       map (+1) $
       generate (constant (Z :. (10::Int))) unindex1

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


-- This test has an map that WILL NOT be pushed through the backpermute.
p16e :: Acc (Vector Float)
p16e = map (+10) $ 
       backpermute sz id $ 
       generate sz (A.fromIntegral . unindex1_int)
 where sz = constant (Z:.(5::Int))

  --     swap = lift1 $ \(Z:.x:.y) -> Z :.      y  :.      x 
  --                               :: Z :. Exp Int :. Exp Int
  -- in
  -- backpermute (swap $ shape mat') swap mat'

--------------------------------------------------------------------------------
-- Reshape:
       
p17a :: Acc (Vector Float)
p17a = reshape (index1 10) p1a

p17b :: Acc (Array DIM2 Float)
p17b = reshape (index2 2 5) p1a


--------------------------------------------------------------------------------
-- Arrays of dynamically computed sizes:
----------------------------------------

-- We seem to be missing a char to int function??
-- p18a :: Acc (Vector Char)
-- p18a = generate (unit (index1 7) ! index0) (A.toEnum . unindex1_int)

p18a :: Acc (Vector Int)
p18a = generate (unit (index1 7) ! index0) unindex1_int

-- Next introduce an EShape construct:
p18b :: Acc (Scalar Int)
p18b = unit$ shapeSize (shape p18a)

-- Do shapeSize on something higher dimensional (4D):
p18c :: Acc (Scalar Int)
p18c = unit$ shapeSize (shape p2d)

-- Do a reshape on something of unknown size:
p18d :: Acc (Vector Int)
p18d = reshape (index1 7) p18a

-- Do a reshape of dynamic size on something of dynamic size.
p18e :: Acc (Vector Int)
p18e = let mystery = unit (index1 7) ! index0 in
       reshape mystery $ 
       generate mystery unindex1_int

-- Do a replicate of dynamic size:
p18f :: Acc (Vector Int)
p18f = let mystery = (unit (index1 7) ! index0) :: Exp (Z:.Int) in
       replicate mystery (unit 40)

--------------------------------------------------------------------------------
-- Testing *all* the scalar primitives:

-- p19a = ...
-- TODO


--------------------------------------------------------------------------------
-- Testing all FOLD variants:

-- TODO



-- | Similar to p1b: fold the inner 5 elements into two.
p20a :: Acc (Array DIM2 Float)
p20a = let xs   = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
           segs :: Acc (Vector Int)
           segs = use$ fromList (Z :. (2::Int)) [2,3::Int]
       in  foldSeg (+) 0 xs segs
-- should yield
-- (1+2) (3+4+5)
-- (6+7) (8+9+10)
--------------
--   3.0 12.0 
--  13.0 27.0 

-- | The same as 20a except with an statically unknown segment size.
p20b :: Acc (Array DIM2 Float)
p20b = let xs   = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
           segs :: Acc (Vector Int)
           segs = use$ fromList (Z :. (2::Int)) [2,3::Int]

           segs2 :: Acc (Vector Int)
           segs2 = generate (unit (index1 2) ! index0) (\ix -> segs ! ix)
           
       in  foldSeg (+) 0 xs segs2

-- | Ditto with fold1seg.
p20c :: Acc (Array DIM2 Float)
p20c = let xs   = use$ fromList (Z :. (2::Int) :. (5::Int)) [1..10::Float]
           segs :: Acc (Vector Int)
           segs = use$ fromList (Z :. (2::Int)) [2,3::Int]

           segs2 :: Acc (Vector Int)
           segs2 = generate (unit (index1 2) ! index0) (\ix -> segs ! ix)
           
       in  fold1Seg (+) xs segs2


--------------------------------------------------------------------------------
-- Testing STENCILs:

-- TODO


--------------------------------------------------------------------------------
-- Testing SCAN:

-- Scan works on Vectors. Does this mean that there is no multidim variant
-- of these?  

p30 :: Acc (Array DIM1 Int)
p30 = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
      in A.scanl (+) (constant 0)  xs


p31 :: Acc (Array DIM1 Int)
p31 = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
      in A.scanr (+) (constant 0) xs


p32 :: Acc (Array DIM1 Int)
p32 = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
      in A.scanl1 (+) xs

p33 :: Acc (Array DIM1 Int)
p33 = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
      in A.scanr1 (+) xs


-- Odd prime versions of Scan

p40a :: Acc (Array DIM1 Int)
p40a = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
       in P.fst $ A.scanl' (+) (constant 0) xs

p40b :: Acc (Scalar Int)
p40b = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
       in P.snd $ A.scanl' (+) (constant 0) xs

p41a :: Acc (Array DIM1 Int)
p41a = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
       in P.fst $ A.scanr' (+) (constant 0) xs

p41b :: Acc (Scalar Int)
p41b = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
       in P.snd $ A.scanr' (+) (constant 0) xs

         
-------------------------------------------------------------------------------- 

-- | Test iteration
p50a :: Acc (Array DIM0 Int)
p50a = A.unit $ A.while (<* 100) (+ 1) 90

p50b :: Acc (Array DIM1 Int) 
p50b = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int] 
           f i = A.iterate i (+1) 0
       in  map f xs 

p50c :: Acc (Vector Int)
p50c = A.map f (use $ fromList (Z:.10) [0..])
  where
    f i = A.while (<* i) (+1) (constant 0)

-- p50b :: Acc (Array DIM0 (Int,Int))
-- p50b = A.unit $ A.while (<* 100) (+ 1) (90,1) 

---------------------------------------------------------------------------
-- Explore Tuples 
--------------------------------------------------------------------------- 

-- zip seems to have problem (accelerate-nofib)  
-- Should parameterise these over shapes... 

p60a :: Acc (Array DIM0 (Int,Int)) 
p60a = let xs = unit $ constant 1
           ys = unit $ constant 2 
       in  A.zip xs ys 

p60b :: Acc (Array DIM0 (Int,Int))
p60b = let xs = unit $ constant 1
           ys = unit $ constant 2 
       in  A.uncurry A.zip (lift (xs,ys))


p60c :: Acc (Array DIM1 (Int,Int)) 
p60c = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
           ys = use$ fromList (Z :. (10::Int)) [10..20::Int]
       in  A.zip xs ys

p60d :: Acc (Array DIM1 (Int,Int)) 
p60d = let xs = use$ fromList (Z :. (10::Int)) [1..10::Int]
           ys = use$ fromList (Z :. (10::Int)) [10..20::Int]
       in  A.uncurry A.zip (lift (xs,ys))

-- fails: There are simpler ways to recreate the failure 
--  only 'use' needed to cause it. 
p60e :: Acc (Array DIM1 (Int,Int)) 
p60e = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [10..20::Int]
       in  A.uncurry A.zip (use (xs,ys)) 


p60f :: Acc (Array DIM1 ((Int,Int),Int)) 
p60f = let xs = use $ fromList (Z :. (10::Int)) [100..110::Int]
       in  A.zip p60e xs

p60g :: Acc (Array DIM1 (Int,Int)) 
p60g = A.map (\x -> let (x' :: Exp (Int,Int) ,x3 ::Exp Int) = unlift x 
                        (x1 :: Exp Int ,x2 :: Exp Int ) = unlift x'
                    in  lift (x1,x2 + x3)) p60f

-- there are tuples at one point 
p60h :: Acc (Array DIM1 Int) 
p60h = let xs = use $ fromList (Z :. (10::Int)) [1..10::Int]
           f x = let (a :: Exp Int ,b :: Exp Int) = unlift x 
                 in a + b 
       in  A.map (\x -> f (lift (x,constant 1) :: Exp (Int,Int))) xs

-- there are nested tuples at one point 
p60i :: Acc (Array DIM1 Int) 
p60i = let xs = use $ fromList (Z :. (10::Int)) [1..10::Int]
           f x = let (a' :: Exp (Int,Int) ,b :: Exp Int) = unlift x 
                     (a :: Exp Int, c :: Exp Int) = unlift a'
                 in a + b + c 
       in  A.map (\x -> f (lift ((lift (x, constant 2):: Exp (Int,Int) ,constant 1)) :: Exp ((Int,Int),Int))) xs

---------------------------------------------------------------------------
-- 

p70 :: Acc (Array DIM1 (((Int,Int), Int), Int))
p70 = let a = p60f 
          xs = use $ fromList (Z :. (10::Int)) [1..10::Int]
      in A.zipWith (\x y -> lift (x,y) :: Exp (((Int,Int),Int),Int)) a xs  

p70a :: Acc (Array DIM1 ((Int, (Int,Int)), Int))
p70a = let a = p60f 
           xs = use $ fromList (Z :. (10::Int)) [1..10::Int]
       in A.zipWith (\x y -> 
                     let (a :: Exp (Int,Int) ,b :: Exp Int ) = unlift x 
                         ba = lift (b,a) :: Exp (Int,(Int,Int))
                     in  lift (ba,y) :: Exp ((Int,(Int,Int)),Int))   a xs  


---------------------------------------------------------------------------
-- 
p80 :: Acc (Array DIM1 (Int,Int)) 
p80 = let xs = fromList (Z :. (10::Int)) [1..10::Int]
          ys = fromList (Z :. (10::Int)) [11..20::Int]
          arrs = use (xs,ys) 
          (xs',ys') = unlift arrs 
      in A.zip xs' ys'

p80a :: Acc (Array DIM1 (Int,Int)) 
p80a = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           arrs = use (xs,ys) 
           (xs',ys') = unlift arrs 
       in A.zip ys' xs'
         
p80b :: Acc (Array DIM1 (Int,Int,Int)) 
p80b = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           arrs = use (xs,ys,zs) 
           (xs',ys', zs') = unlift arrs 
       in map (\x -> let (x1' :: Exp (Int,Int),z1 :: Exp Int) = unlift x
                         (x1 :: Exp Int, y1 :: Exp Int) = unlift x1'
                     in lift (x1,y1,z1) :: Exp (Int,Int,Int)) (A.zip (A.zip xs' ys') zs') 

p80c :: Acc (Array DIM1 (Int,Int,Int)) 
p80c = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           arrs = use (xs,ys,zs) 
           (xs',ys', zs') = unlift arrs 
       in map (\x -> let (x1' :: Exp (Int,Int),z1 :: Exp Int) = unlift x
                         (x1 :: Exp Int, y1 :: Exp Int) = unlift x1'
                     in lift (x1,y1,z1) :: Exp (Int,Int,Int)) (A.zip (A.zip ys' zs') xs')

p80d :: Acc (Array DIM1 (Int,Int,Int)) 
p80d = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           arrs = use (xs,ys,zs) 
           (xs',ys', zs') = unlift arrs 
       in map (\x -> let (x1' :: Exp (Int,Int),z1 :: Exp Int) = unlift x
                         (x1 :: Exp Int, y1 :: Exp Int) = unlift x1'
                     in lift (x1,y1,z1) :: Exp (Int,Int,Int)) (A.zip (A.zip zs' xs') ys')



p80e :: Acc (Array DIM1 (Int,Int)) 
p80e = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (5::Int)) [1..5::Int]
           arrs = use (xs,ys) 
           (xs',ys') = unlift arrs 
       in A.zip xs' ys'
 

-- completely explodes!
--p80b :: Acc (Array DIM1 Int,Array DIM2 Int)
--p80b = let xs = fromList (Z :. (10::Int)) [1..10::Int]
--           ys = fromList (Z :. (2::Int) :. (5::Int)) [1..10::Int]
--           arrs = use (xs,ys)
--       in arrs


p90 :: Acc ((Array DIM1 Int)
            ,(Array DIM1 Int)
            ,(Array DIM1 Int)) 
p90 = let xs = fromList (Z :. (10::Int)) [1..10::Int]
          ys = fromList (Z :. (10::Int)) [11..20::Int]
          zs = fromList (Z :. (10::Int)) [21..30::Int]
          arrs = lift (use xs, use ys, use zs)
      in arrs

p90a :: Acc (Array DIM1 Int)
p90a = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           arrs :: Acc ((Array DIM1 Int)
                        ,(Array DIM1 Int)
                        ,(Array DIM1 Int)) = lift (use xs, use ys, use zs) 
           (x,y,z) :: ( Acc (Array DIM1 Int)
                      , Acc (Array DIM1 Int)
                      , Acc (Array DIM1 Int)) = unlift arrs
       in x

p90b :: Acc (Array DIM1 Int)
p90b = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           arrs :: Acc ((Array DIM1 Int)
                        ,(Array DIM1 Int)
                        ,(Array DIM1 Int)) = lift (use xs, use ys, use zs) 
           (x,y,z) :: ( Acc (Array DIM1 Int)
                      , Acc (Array DIM1 Int)
                      , Acc (Array DIM1 Int)) = unlift arrs
       in y
p90c :: Acc (Array DIM1 Int)
p90c = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           arrs :: Acc ((Array DIM1 Int)
                        ,(Array DIM1 Int)
                        ,(Array DIM1 Int)) = lift (use xs, use ys, use zs)
           (x,y,z) :: ( Acc (Array DIM1 Int)
                      , Acc (Array DIM1 Int)
                      , Acc (Array DIM1 Int)) = unlift arrs
       in z
---------------------------------------------------------------------------
-- 


p91 :: Acc (Array DIM1 (Int,Int), 
            Array DIM1 (Int,Int) ) 
p91 = let xs = fromList (Z :. (10::Int)) [1..10::Int]
          ys = fromList (Z :. (10::Int)) [11..20::Int]
          zs = fromList (Z :. (10::Int)) [21..30::Int]
          ws = fromList (Z :. (10::Int)) [31..40::Int]
          arrs1 = use (xs,ys)
          arrs2 = use (zs,ws) 
          (xs',ys') = unlift arrs1
          (zs',ws') = unlift arrs2 
      in lift (A.zip xs' ys', A.zip zs' ws')

p91a :: Acc (Array DIM1 (Int,Int), 
            Array DIM1 (Int,Int) ) 
p91a = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           ws = fromList (Z :. (10::Int)) [31..40::Int]
           arrs1 = use (xs,ys)
           arrs2 = use (zs,ws) 
           (xs',ys') = unlift arrs1
           (zs',ws') = unlift arrs2 
       in lift (A.zip zs' ys', A.zip xs' ws')

p91b :: Acc (Array DIM1 (Int,Int), 
            Array DIM1 (Int,Int) ) 
p91b = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           ws = fromList (Z :. (10::Int)) [31..40::Int]
           arrs1 = use (xs,ys)
           arrs2 = use (zs,ws) 
           (xs',ys') = unlift arrs1
           (zs',ws') = unlift arrs2 
       in lift (A.zip xs' ws', A.zip zs' ys')

p91c :: Acc (Array DIM1 (Int,Int), 
            Array DIM1 (Int,Int) ) 
p91c = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           ws = fromList (Z :. (10::Int)) [31..40::Int]
           arrs1 = use (xs,ys)
           arrs2 = use (zs,ws) 
           (xs',ys') = unlift arrs1
           (zs',ws') = unlift arrs2 
       in lift (A.zip ws' ys', A.zip zs' xs')

p91d :: Acc (Array DIM1 (Int,Int), 
             Array DIM1 (Int,Int) ) 
p91d = let xs = fromList (Z :. (10::Int)) [1..10::Int]
           ys = fromList (Z :. (10::Int)) [11..20::Int]
           zs = fromList (Z :. (10::Int)) [21..30::Int]
           ws = fromList (Z :. (10::Int)) [31..40::Int]
           xs' = use xs
           ys' = use ys
           zs' = use zs
           ws' = use ws
       in lift (A.zip xs' ys', A.zip zs' ws')


-- This program sends backendkit into infinite loop. 
p92 :: Acc (Array DIM1 (Int,Int),
            Array DIM1 (Int,Int))
p92 = let xs = fromList (Z :. (10::Int)) (Prelude.zip [1..10::Int] [11..20::Int])
          ys = fromList (Z :. (10::Int)) (Prelude.zip [21..30::Int] [31..40::Int])
          arrs1 = use xs
          arrs2 = use ys
          (xs',ys') :: (Acc (Array DIM1 Int), Acc (Array DIM1 Int)) = A.unzip arrs1 
          (zs',ws') :: (Acc (Array DIM1 Int), Acc (Array DIM1 Int)) = A.unzip arrs2 
      in lift (A.zip xs' ys', A.zip zs' ws')

p92a :: Acc (Array DIM1 (Int,Int))
p92a = let xs = fromList (Z :. (10::Int)) (Prelude.zip [1..10::Int] [11..20::Int])
           arrs1 = use xs
           (xs',ys') :: (Acc (Array DIM1 Int), Acc (Array DIM1 Int)) = A.unzip arrs1 
       in A.zip xs' ys'



--------------------------------------------------------------------------------
-- Let's print matrices nicely.

padleft n str | P.length str >= n = str
padleft n str | otherwise         = P.take (n - P.length str) (repeat ' ') ++ str

class NiceShow a where
  pp :: a -> String
        
instance Show a => NiceShow (Array DIM1 a) where
  pp arr = 
    capends$ concat$ 
    intersperse " " $
    P.map (padleft maxpad) ls 
   where 
         ls   = P.map show $ toList arr
         maxpad = P.maximum$ P.map P.length ls

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
         maxpad = P.maximum$ P.map P.length ls
         rowls = chunksOf cols ls

--------------------------------------------------------------------------------

convertToSimpleProg :: Sug.Arrays a => Sm.Acc a -> S.Prog ()
convertToSimpleProg = phase1 . phase0

