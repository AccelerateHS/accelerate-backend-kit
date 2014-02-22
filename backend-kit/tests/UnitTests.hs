{-# LANGUAGE TypeOperators #-}
module Main where
import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Array,Z,(:.))
import Data.Array.Accelerate.BackendKit.Tests as T
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as IR1
import Data.Array.Accelerate.BackendKit.SimpleArray as SA
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone (packArray, repackAcc)

unitArray :: AccArray
unitArray = AccArray [10] [ArrayPayloadUnit 10]

unitPacked :: Array (Z :. Int) ()
unitPacked = packArray unitArray

-- case_packUnits = assertEqual """Array (Z :. 10) [(),(),(),(),(),(),(),(),(),()]" (show unitPacked)

case_printUnits :: IO ()
case_printUnits = do
  putStrLn $ "unitArray " ++ show unitArray
  putStrLn $ "unitPacked " ++ show unitPacked

main :: IO ()
main = do
  case_printUnits
  
