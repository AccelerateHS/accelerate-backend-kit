{-# LANGUAGE NamedFieldPuns #-}

-- | This module provides a pass that performs type checking and other
-- invariant-validation for the SimpleAcc datatype.
--
-- It does NOT encode all the (shifting) invariants between different passes of the
-- compiler, just the ones that always hold.
module Data.Array.Accelerate.BackendKit.Phase1.VerifySimpleAcc
       (
         verifySimpleAcc
       )
       where

import Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S 
import Prelude as P

-- Attempt to typecheck a program, returning Nothing if it checks out,
-- or an error message if there is a probem.
verifySimpleAcc :: Prog a -> Maybe String
verifySimpleAcc prog@Prog{progBinds, progResults, progType } =
  -- The rule for progResults is that their types match a flattened version of the result type:
  if resTys /= expectedTys then
    mismatchErr "Result type" resTys expectedTys
    else Nothing -- FINISHME
  where
    resTys      = P.map envlkp (resultNames progResults)
    envlkp vr   = case M.lookup vr env of
                    Nothing -> error$"SimpleAcc.hs/typeCheckProg: no binding for progResult: "++show vr
                    Just x  -> x 
    expectedTys = flattenTy progType
    env         = progToEnv prog

    mismatchErr msg got expected = Just$ msg++" does not match expected. "++
                                   "\nGot:      "++show got ++
                                   "\nExpected: "++show expected

