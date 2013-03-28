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
import Prelude as P hiding (or) 
--------------------------------------------------------------------------------

type Env = M.Map Var Type
type ErrorMessage = String

-- Attempt to typecheck a program, returning Nothing if it checks out,
-- or an error message if there is a probem.
verifySimpleAcc :: Prog a -> Maybe String
verifySimpleAcc prog@Prog{progBinds, progResults, progType } =
  -- The rule for progResults is that their types match a flattened version of the result type:
    (assertTyEq "Result type" resTys expectedTys) `or`
    (not (all hasArrayType resTys) ? 
      ("Final result of program includes non-array:"
       ++show(P.filter (not . hasArrayType) resTys))) `or`
    -- (verifyUnique "Result names" (resultNames progResults)) `or`
    -- (verifyUnique "Top level bindings" topBinds) `or`
    (doBinds env progBinds)
  where
    resTys      = P.map envlkp (resultNames progResults)
    envlkp vr   = case M.lookup vr env of
                    Nothing -> error$"SimpleAcc.hs/typeCheckProg: no binding for progResult: "++show vr
                    Just x  -> x 
    expectedTys = flattenTy progType
    env         = progToEnv prog

    topBinds = []


verifyUnique = error "verifyUnique"

mismatchErr :: (Show a, Show a1) => String -> a -> a1 -> String
mismatchErr msg got expected = msg++" does not match expected. "++
                               "\nGot:      "++show got ++
                               "\nExpected: "++show expected

assertTyEq :: (Eq a, Show a) => String -> a -> a -> Maybe String
assertTyEq msg got expected =
  if got == expected
  then Nothing
  else Just$ mismatchErr msg got expected
  

doBinds :: Env -> [ProgBind t] -> Maybe ErrorMessage
doBinds _env [] = Nothing
doBinds env (ProgBind vo ty _ (Right ae) :rst) =
  doAE ty env ae `or`
  doBinds env rst
doBinds env (ProgBind vo ty _ (Left ex) :rst) =
  assertTyEq ("Top-level scalar variable "++show vo)
             (recoverExpType env ex) ty `or`
  doBinds env rst
  
doAE :: Type -> Env -> AExp -> Maybe ErrorMessage
doAE outTy env ae =
  case ae of
    Use arr -> verifyAccArray outTy arr
    Vr v    -> lkup v $ \ty -> assertTyEq ("Varref "++show v) ty outTy
    _ -> Nothing                       
--     Map fn vr           -> addArrRef vr $ doFn1 fn mp
--     ZipWith fn2 v1 v2   -> addArrRef v1 $ addArrRef v2 $ doFn2 fn2 mp
--     Cond e1 v1 v2       -> addArrRef v1 $ addArrRef v2 $ doE e1 mp
--     Generate e1 fn1     -> doE e1       $ doFn1 fn1 mp

--     Fold fn e1 vr       -> addArrRef vr$ doE e1 $ doFn2 fn mp
--     Fold1  fn vr        -> addArrRef vr$          doFn2 fn mp
--     FoldSeg fn e1 v1 v2 -> addArrRef v1 $ addArrRef v2 $
--                            doE e1       $ doFn2 fn mp 
--     Fold1Seg  fn v1 v2  -> addArrRef v1 $ addArrRef v2 $ doFn2 fn mp
--     Scanl  fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
--     Scanl' fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
--     Scanl1 fn2     vr   -> addArrRef vr $                doFn2 fn2 mp
--     Scanr  fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
--     Scanr' fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
--     Scanr1 fn2     vr   -> addArrRef vr $                doFn2 fn2 mp
--     Permute fn2 v1 fn1 v2 -> addArrRef v1 $ addArrRef v2 $
--                              doFn1 fn1    $ doFn2 fn2 mp
--     Backpermute e1 fn1 vr -> addArrRef vr $ doE e1 $ doFn1 fn1 mp
--     Stencil fn1 _b vr     -> addArrRef vr $ doFn1 fn1 mp
--     Stencil2 fn2 _b1 v1 _b2 v2 -> addArrRef v1 $ addArrRef v2 $ doFn2 fn2 mp

--     Reshape e1 vr       -> addArrRef vr $ doE e1 mp
--     Replicate _slt e1 vr -> addArrRef vr $ doE e1 mp
--     Index _slt vr e1     -> addArrRef vr $ doE e1 mp
--     Unit _ -> error "trackUses: Unit is not part of the grammar accepted by this pass"

 where
   lkup v k =
     case M.lookup v env of
       Just x  -> k x
       Nothing -> Just$ "Unbound variable: "++show v
      
-- doFn1 :: Fun1 Exp -> UseMap -> UseMap
-- doFn1 (Lam1 _ exp) mp = doE exp mp 

-- doFn2 :: Fun2 Exp -> UseMap -> UseMap
-- doFn2 (Lam2 _ _ exp) mp = doE exp mp 


-------------------------------------------------------------------------------

or :: Maybe ErrorMessage -> Maybe ErrorMessage -> Maybe ErrorMessage 
or (Just x) (Just y) = Just (x++"\n"++y)
or (Just x) Nothing = Just x
or Nothing (Just x) = Just x
or Nothing Nothing  = Nothing

(?) :: Bool -> ErrorMessage -> Maybe ErrorMessage
True ? m  = Just m
False ? _ = Nothing
