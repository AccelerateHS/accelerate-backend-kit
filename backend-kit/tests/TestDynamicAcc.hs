{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Data.Array.Accelerate.DynamicAcc2

import           Data.Array.Accelerate as A hiding ((++))
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..), FloatPrim(..))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.Tests (allProgs, allProgsMap, TestEntry(..), AccProg(..))
import           Data.Array.Accelerate.Interpreter as I
import qualified Data.Array.Unboxed as U
import           Data.Map as M
import           Prelude as P 
import qualified Test.Framework as TF
import           Test.Framework.Providers.HUnit (testCase)
import           Test.Framework.TH (testGroupGenerator)
import qualified Test.HUnit as H 

--------------------------------------------------------------------------------  
-- Misc, Tests, and Examples
--------------------------------------------------------------------------------  


{-
-- Small tests:
t0 :: SealedAcc
t0 = convertClosedAExp $
     S.Use (S.AccArray [5,2] (payloadsFromList1$ P.map I [1..10]))
t0b :: Acc (Array DIM2 (Int))
t0b = downcastA t0
-}

t1 = -- convertClosedExp
     convertOpenExp emptyEnvPack 
     (S.ECond (S.EConst (B True)) (S.EConst (I 33)) (S.EConst (I 34)))
t1_ :: A.Exp Int
t1_ = downcastE t1
case_if = H.assertEqual "if and const" (show t1_) "33"

t2 :: SealedExp
t2 = convertOpenExp emptyEnvPack 
     (S.ELet (v, TInt, (S.EConst (I 33))) (S.EVr v))
 where v = S.var "v" 
t2_ :: Exp Int
t2_ = downcastE t2
case_const = H.assertEqual "simple const" (show t2_) "33"

t4 = roundTrip (allProgsMap M.! "p4")

t5 = convertOpenAcc emptyEnvPack (S.Unit (S.EConst (I 33)))
t5_ :: Acc (Scalar Int)
t5_ = downcastA t5
case_unit = H.assertEqual "unit array" (show$ I.run t5_) "Array (Z) [33]"

t6 = convertOpenAcc (extendA arr (TArray 0 TInt) t5 emptyEnvPack)
        (S.Map (S.Lam1 (v,TInt) (S.EVr v)) arr)
  where v   = S.var "v"
        arr = S.var "arr"
t6_ :: Acc (Scalar Int)
t6_ = downcastA t6
case_mapId = H.assertEqual "map id function" (show$ I.run t6_) "Array (Z) [33]"


t7 = convertOpenAcc (extendA arr (TArray 0 TInt) t5 emptyEnvPack)
        (S.Map (S.Lam1 (v,TInt) (S.EPrimApp TInt (S.NP S.Add) [S.EVr v, S.EVr v])) arr)
  where v   = S.var "v"
        arr = S.var "arr"
t7_ :: Acc (Scalar Int)
t7_ = downcastA t7
case_mapAdd = H.assertEqual "map add fun" (show$ I.run t7_) "Array (Z) [66]"

t8 = convertOpenExp emptyEnvPack (S.ETuple [S.EConst (I 11), S.EConst (F 3.3)])
t8_ :: Exp (Int,Float)
t8_ = downcastE t8
case_pairExp = H.assertEqual "simple pair"
             (show $ I.run$ A.unit t8_)
--             (A.fromList Z [(11,3.3)]) -- Why is there no EQ for Accelerate arrays?
             "Array (Z) [(11,3.3)]"


t8b = convertOpenExp emptyEnvPack (S.ETuple [S.EConst (I 11), S.EConst (F 3.3), S.EConst (W 99)])
t8b_ :: Exp (Int,Float,Word)
t8b_ = downcastE t8

t8c = convertAcc (S.Unit (S.ETuple [S.EConst (I 11), S.EConst (F 3.3), S.EConst (W 99)]))

t8d = convertAcc (S.Unit (S.ETuple [S.EConst (I 11), S.ETuple [S.EConst (F 3.3), S.EConst (W 99)]]))


t9 = convertOpenAcc emptyEnvPack $
     S.Use$ S.AccArray [10] [S.ArrayPayloadInt (U.listArray (0,9) [1..10])]
t9_ :: Acc (Vector Int)
t9_ = downcastA t9
case_use = H.assertEqual "use array" (show $ I.run$ t9_)
           "Array (Z :. 10) [1,2,3,4,5,6,7,8,9,10]"

t10 = convertOpenAcc emptyEnvPack $
      S.Generate (S.EConst (I 10)) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v,TInt) (S.EVr v))
  where v   = S.var "v"
t10_ :: Acc (Vector Int)
t10_ = downcastA t10
case_generate1 = H.assertEqual "generate1" (show $ I.run$ t10_)
                 "Array (Z :. 10) [0,1,2,3,4,5,6,7,8,9]"

t11 = convertOpenAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2)]) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v, TTuple [TInt,TInt]) (S.EVr v))
  where v   = S.var "v"
t11_ :: Acc (Array DIM2 (Int,Int))
t11_ = downcastA t11
case_generate2D = H.assertEqual "generate2" (show $ I.run$ t11_)
                 "Array (Z :. 3 :. 2) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]"

-- | This test exercises only tuples on the input side, plus tuple field projection.
t12 = convertOpenAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2)]) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v, TTuple [TInt,TInt]) (S.ETupProject 0 1 (S.EVr v)))
  where v   = S.var "v"
t12_ :: Acc (Array DIM2 Int)
t12_ = downcastA t12
case_generatePrj = H.assertEqual "generate3"
                   (show$ I.run$ t12_)
                   (show$ I.run t12A)
--                   "Array (Z :. 3 :. 2) [0,0,1,1,2,2]"
-- Manually translated version:
t12A = A.generate (constant (Z :. (3::Int) :. (2 :: Int)))
                  (\x0 -> indexHead (indexTail x0))

v = S.var "v"

-- | Now project TWO components out of THREE.
t13 = convertOpenAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2), S.EConst (I 1)]) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v, TTuple [TInt,TInt,TInt])
                    (S.ETupProject 1 2 (S.EVr v)))
t13_ :: Acc (Array DIM3 (Int,Int))
t13_ = downcastA t13
case_generatePrj2 = H.assertEqual "generate4"
                   (show$ I.run$ t13_)
                   "Array (Z :. 3 :. 2 :. 1) [(0,0),(1,0),(0,0),(1,0),(0,0),(1,0)]"
                   -- (show$ I.run t12A)

-- This is the program that matches t13_.  Whether that is correct we should audit.
ref13 = A.generate (constant (Z :. (3::Int) :. (2 :: Int) :. (1 :: Int)))
          (\x -> let a,b,c :: Exp Int
                     (Z :. a :. b :. c) = unlift x
                 in lift (b,c))

-- | Generate an array of shapes -- this is tricky because in
-- SimpleAcc we represent shapes merely as tuples.
t14 = convertOpenAcc emptyEnvPack $
--      S.Generate (S.ETuple [S.EConst (I8 3), S.EConst (I16 2), S.EConst (I32 1)]) -- This should be a typechecking error
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2), S.EConst (I 1)]) 
                 (S.Lam1 (v, TTuple [TInt,TInt,TInt]) (S.EVr v))
-- t14_ :: Acc (Array DIM3 (Int,(Int,Int)))
-- t14_ :: Acc (Array DIM3 (Int,Int,Int))
t14_ :: Acc (Array DIM3 (Z :. Int :. Int :. Int))
t14_ = downcastA t14
case_t14_generate = H.assertEqual "generate5"
                   (show$ I.run$ t14_)
                   "Array (Z :. 3 :. 2 :. 1) [(0,0,0),(0,1,0),(1,0,0),(1,1,0),(2,0,0),(2,1,0)]"
--                 "Array (Z :. 3 :. 2 :. 1) [(0,(0,0)),(0,(1,0)),(1,(0,0)),(1,(1,0)),(2,(0,0)),(2,(1,0))]"

ref14 = A.generate (constant (Z :. (3::Int) :. (2 :: Int) :. (1 :: Int)))
          (\x -> let a,b,c :: Exp Int
                     (Z :. a :. b :. c) = unlift x
                 in lift (a,(b,c)))

i15 = convertOpenAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2), S.EConst (I 1)]) 
                 (S.Lam1 (v, TTuple [TInt,TInt,TInt])
                  (S.ETuple [ S.ETuple [(S.ETupProject 0 1 (S.EVr v)),
                                       (S.ETupProject 1 1 (S.EVr v))],
                             (S.ETupProject 2 1 (S.EVr v)) ])
                 )
  where v   = S.var "v"
i15_ :: Acc (Array DIM3 ((Int,Int),Int))
i15_ = downcastA i15
case_generateTupLeftNest = H.assertEqual "generate6"
                           (show$ I.run$ i15_)
                           "Array (Z :. 3 :. 2 :. 1) [((0,0),0),((0,1),0),((1,0),0),((1,1),0),((2,0),0),((2,1),0)]"

--------------------------------------------------


t20 = convertExp $ S.EPrimApp TBool (S.SP S.Gt) [S.EConst (I 1), S.EConst (I 2)]
t20_ :: Exp Bool
t20_ = downcastE t20
case_gt = H.assertEqual "t20_" (show t20_) "False"


t21 = convertExp $ S.EPrimApp TBool (S.SP S.Eq) [S.EConst (I 11), S.EConst (I 11)]
t21_ :: Exp Bool
t21_ = downcastE t21
case_eq = H.assertEqual "t21_" (show t21_) "True"

--------------------------------------------------
-- Test PrimApps:

p1 = convertOpenExp emptyEnvPack
        (S.EPrimApp TInt (S.NP S.Add) [S.EConst (I 1), S.EConst (I 2)])
p1_ :: Exp Int
p1_ = downcastE p1

case_primApp_Add = H.assertEqual "primapp_add" (show p1_) "3"

p2 = convertOpenExp emptyEnvPack
        (S.EPrimApp TInt (S.NP S.Sig) [S.EConst (I (-11))])
p2_ :: Exp Int
p2_ = downcastE p2
case_primApp_Sig = H.assertEqual "primapp_sig" (show p2_) "-1"

p3 = convertOpenExp emptyEnvPack
        (S.EPrimApp TInt (S.FP Round) [S.EConst (F (9.99))])
p3_ :: Exp Int
p3_ = downcastE p3
case_primApp_Round = H.assertEqual "primapp_sig" (show p3_) "10"

--------------------------------------------------
-- Test Constant conversion

c0 :: SealedExp
c0 = constantE (I 99)
c0_ :: A.Exp Int
c0_ = downcastE c0

c1 :: SealedEltTuple
c1 = scalarTypeD (TTuple [TInt, TInt32, TInt64])

c2 :: SealedEltTuple
c2 = scalarTypeD (TTuple [TTuple [TInt, TInt32], TInt64])

case_const0 :: H.Assertion
case_const0 = H.assertEqual "int const" (show c0_) "99"

-- We ARE using surface tuple types for now:
case_const1 :: H.Assertion
case_const1 = H.assertEqual "tuple repr 1"
            (show c1)  "Sealed:(Int,Int32,Int64)"
            
case_const2 :: H.Assertion
case_const2 = H.assertEqual "tuple repr 2"
            (show c2) "Sealed:((Int,Int32),Int64)"

--------------------------------------------------
-- Complete program unit tests

allProg_tests :: TF.Test
allProg_tests = TF.testGroup "Backend kit unit tests" $
                [ testCase ("progtest_"++name te) (roundTrip te)
                | te <- allProgs ]

-- Note, most don't work yet, as expecte,d [2013.08.14] but check out
-- p12e, which seems to indicate a bug.

roundTrip :: TestEntry -> IO ()
roundTrip TestEntry{name, simpleProg, origProg= AccProg (acc :: Acc aty) } = do 
  let cvt :: Acc aty
      cvt = downcastA $ convertProg simpleProg
  dbgtrace ("RoundTripping:\n" ++ show acc) $ 
   H.assertEqual ("roundTrip "++name)
                 (show$ I.run cvt)
                 (show$ I.run acc)

--------------------------------------------------
-- Aggregate tests:

main :: IO ()
main = TF.defaultMain [unitTests]

unitTests :: TF.Test
unitTests =
  TF.testGroup "AllTests" [
    $(testGroupGenerator),
    allProg_tests
  ]

