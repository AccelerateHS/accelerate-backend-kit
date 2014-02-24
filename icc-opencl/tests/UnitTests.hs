

module Main where

import Control.Monad
import Data.Array.Accelerate.C as C
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendClass as BC
import Data.Array.Unboxed as U
import qualified Data.Map as M

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit (assertEqual)
--------------------------------------------------------------------------------

fromList ls = U.listArray (0, length ls - 1) ls

t1 = do 
  let bkend = C.defaultBackend
  let arr = AccArray [3] [ArrayPayloadFloat (fromList [1.1, 2.2, 3.3]),
                          ArrayPayloadInt   (fromList [4,5,6])]
  let vr  = var "vr"
      typ = TArray 1 (TTuple [TFloat,TInt])
  let prog = S.Prog { progBinds   = [ProgBind vr typ () (Right (S.Use arr))]
                    , progType    = typ
                    , progResults = WithoutShapes [vr]
                    , uniqueCounter = 1000
                    , typeEnv = M.empty }
  remt  <- BC.simpleRunRaw bkend (Just "UnitTests.t1") prog Nothing
  payloads <- mapM (BC.simpleCopyToHost bkend) remt

  putStrLn $ "Round tripped: "++show payloads
--  assertEqual "Round trip copy leaves same array" arr arr2
  return ()

main = do 
  t1

