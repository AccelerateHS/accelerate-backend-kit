{-# LANGUAGE TypeOperators #-}
module Main where
import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Array,Z,(:.))
import Data.Array.Accelerate.BackendKit.Tests as T
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as IR1
import Data.Array.Accelerate.BackendKit.SimpleArray as SA
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone (packArray, repackAcc)

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit (assertEqual)
------------------------------------------------------------

unitArray :: AccArray
unitArray = AccArray [10] [ArrayPayloadUnit 10]

unitPacked :: Array (Z :. Int) ()
unitPacked = packArray unitArray

case_packUnits = assertEqual """Array (Z :. 10) [(),(),(),(),(),(),(),(),(),()]" (show unitPacked)

case_printUnits :: IO ()
case_printUnits = do
  putStrLn $ "unitArray " ++ show unitArray
  putStrLn $ "unitPacked " ++ show unitPacked

-- Scalar:
-- zPacked0 :: Array Z Z
-- zPacked0 = packArray $ AccArray [1] [ArrayPayloadUnit 1]

zPacked1 :: Array (Z :. Int) Z
zPacked1 = packArray unitArray

case_zPacked = assertEqual "zPacked " "Array (Z :. 10) [Z,Z,Z,Z,Z,Z,Z,Z,Z,Z]" (show zPacked1)

zPacked2 :: Array (Z :. Int) Z
-- zPacked2 = repackAcc (undefined :: A.Acc (A.Array (Z :. Int) Z)) [unitArray]
zPacked2 = repackAcc (A.use zPacked1) [unitArray]

main :: IO ()
main = do
  case_printUnits
  case_packUnits
  case_zPacked

  putStrLn$ "zpacked "++ show zPacked1

  putStrLn "zPacked2:"
  print zPacked2
