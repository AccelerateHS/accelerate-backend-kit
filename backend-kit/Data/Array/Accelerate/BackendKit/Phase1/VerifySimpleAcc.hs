{-# LANGUAGE NamedFieldPuns #-}

-- | This module provides a pass that performs type checking and other
-- invariant-validation for the SimpleAcc datatype.
--
-- It does NOT encode all the (shifting) invariants between different passes of the
-- compiler, just the ones that always hold.
module Data.Array.Accelerate.BackendKit.Phase1.VerifySimpleAcc
       (
         verifySimpleAcc, VerifierConfig(..), DimCheckMode(..),
       )
       where

import Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendKit.SimpleArray (verifyAccArray)
import Prelude as P hiding (or) 
--------------------------------------------------------------------------------

-- | It would be difficult to capture all the changing grammars/invarinats between
-- passes, but we do parameterize this pass by some choices:
data VerifierConfig =
  VerifierConfig {    
    dimMode :: DimCheckMode
  }

data DimCheckMode
  = NDim   -- ^ N-dimensional, fully typed.
  | OneDim -- ^ All arrays expected to be 1D
  | NoDim  -- ^ Ignore dimension mismatches.
 deriving (Eq,Show,Read,Ord)

type Env = M.Map Var Type
type ErrorMessage = String

-- Attempt to typecheck a program, returning Nothing if it checks out,
-- or an error message if there is a probem.
verifySimpleAcc :: VerifierConfig -> Prog a -> Maybe String
verifySimpleAcc cfg@(VerifierConfig{dimMode}) prog@Prog{progBinds, progResults, progType } =
  -- The rule for progResults is that their types match a flattened version of the result type:
    (foldl1 (or) (zipWith (assertTyEqual dimMode "Result type") resTys expectedTys)) `or`
    (not (all hasArrayType resTys) ? 
      ("Final result of program includes non-array:"
       ++show(P.filter (not . hasArrayType) resTys))) `or`
    -- (verifyUnique "Result names" (resultNames progResults)) `or`
    -- (verifyUnique "Top level bindings" topBinds) `or`
    (doBinds cfg env progBinds)
  where
    resTys      = P.map envlkp (resultNames progResults)
    envlkp vr   = case M.lookup vr env of
                    Nothing -> error$"SimpleAcc.hs/typeCheckProg: no binding for progResult: "++show vr
                    Just x  -> x 
    expectedTys = flattenTy progType
    env         = progToEnv prog

    topBinds = []


-- verifyUnique = error "verifyUnique"

mismatchErr :: (Show a, Show a1) => String -> a -> a1 -> String
mismatchErr msg got expected = msg++" does not match expected. "++
                               "\nGot:      "++show got ++
                               "\nExpected: "++show expected

assertTyEqual :: DimCheckMode -> String -> Type -> Type -> Maybe String
assertTyEqual NoDim msg (TArray d1 e1) (TArray d2 e2) = assertTyEqual NoDim msg e1 e2
assertTyEqual _ msg got expected =
  if got == expected
  then Nothing
  else Just$ mismatchErr msg got expected


doBinds :: VerifierConfig -> Env -> [ProgBind t] -> Maybe ErrorMessage
doBinds _cfg _env [] = Nothing
doBinds cfg env (ProgBind vo ty _ (Right ae) :rst) =
  doAE cfg ty env ae `or`
  doBinds cfg env rst
doBinds cfg@(VerifierConfig{dimMode}) env (ProgBind vo ty _ (Left ex) :rst) =
  assertTyEqual dimMode ("Top-level scalar variable "++show vo)
                        (recoverExpType env ex) ty `or`
  doBinds cfg env rst

-- TODO: Simplify handling of AExps by introducing an arrow type, and coming up with
-- some direct representation of the type of each AExp op.
-- data TmpType = Arrow TmpType TmpType | TVar Int | PlainType Type

doAE :: VerifierConfig -> Type -> Env -> AExp -> Maybe ErrorMessage
doAE VerifierConfig{dimMode} outTy env ae =
  case ae of
    Use arr -> verifyAccArray outTy arr
    Vr v    -> lkup v $ \ty -> assertTyEq ("Varref "++show v) ty outTy
    Map fn vr               ->      
      let (it,ot,err) = typeFn1 "Map" fn in
      err `or`
      assertTyEq "Map result" ot out_elty `or`
      arrVariable vr (TArray out_dim it)

    ZipWith fn2 v1 v2   ->
      let (it1,it2,ot,err) = typeFn2 "ZipWith" fn2 in
      err `or`
      assertTyEq "ZipWith result" ot out_elty `or`
      arrVariable v1 (TArray out_dim it1) `or`
      arrVariable v2 (TArray out_dim it2)
      
    Cond e1 v1 v2 -> expr "Array-level conditional test" e1 TBool `or`
                     arrVariable v1 outTy `or`
                     arrVariable v2 outTy 
    Generate e1 fn1 ->
      let (it,ot,err) = typeFn1 "Generate" fn1
          e1ty = recoverExpType env e1 in 
      err `or`
      assertTyEq "Generate index exp" e1ty it  `or`
      assertTyEq "Generate output" (TArray out_dim ot) outTy 

    Fold fn e1 vr ->
      let (elt,err) = foldHelper "Fold" fn vr in
      err `or` expr  "Fold initializer" e1 elt
    Fold1  fn vr ->
      snd$ foldHelper "Fold1" fn vr

    Unit e1 ->
      assertEq "Unit output dimension" out_dim 0 `or`
      expr "Unit input expression" e1 out_elty
    Replicate tmplt e1 vr | dimMode==NDim ->
      let numFixed = length$ P.filter (==Fixed) tmplt
          numAll   = length$ P.filter (==All) tmplt
          exprTy   = recoverExpType env e1 
      in
       arrVariable vr (TArray numAll out_elty) `or`
       assertEq "Template length in Replicate" (length tmplt) out_dim 

-- FIXME: The encoding has the obnoxious problem that it ELIDES unit entries on one end:
       -- (shapeType exprTy $ \ len -> 
       --    assertTyEq "Number of components in replicate scalar expr"
       --               -- The scalar expression includes the new and old dims:
       --               len (length tmplt))
       
    Replicate {} | dimMode==OneDim -> Just"Should NOT see a Replicate after OneDimensionalize"    
    Replicate {} | dimMode==NoDim  -> Nothing -- Is there anything left to check here?

    Backpermute e1 fn1 vr ->
      let (it,ot,err) = typeFn1 "Backpermute" fn1
          shpTy = recoverExpType env e1 in 
      err `or`
      assertTyEq "Backpermute index function input" shpTy it `or`
      -- (shapeType shpTy $ \len -> 
      --   assertTyEq "Backpermute shape expression" len out_dim) `or`
      (shapeType ot $ \inDim ->
       arrVariable vr (TArray inDim out_elty))


    -- TODO: FINISHME:
    Reshape e1 vr     -> Nothing
    Index tmplt vr e1 -> Nothing

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
--     Stencil fn1 _b vr     -> addArrRef vr $ doFn1 fn1 mp
--     Stencil2 fn2 _b1 v1 _b2 v2 -> addArrRef v1 $ addArrRef v2 $ doFn2 fn2 mp

    _ -> error$"FINISHME: Unhandled operator in verifySimpleAcc:\n"++show ae
    
 where
   TArray out_dim out_elty = outTy

   checkDims = case dimMode of
                 OneDim -> True
                 NDim   -> True
                 NoDim  -> False
   ifCheckDims x | checkDims = x
                 | otherwise = Nothing
   -- mkTArray d t | checkDims = mkTArray d t
   --              | otherwise = TArray (-1) t

   foldHelper variant fn vr =    
      let (it1,it2,ot,err) = typeFn2 variant fn in
      (it1,
       err `or`
       assertTyEq (variant++" arguments not the same type") it1 it2 `or`
       assertTyEq (variant++" output not expected type") it1 ot `or`
       assertTyEq (variant++" output") (TArray out_dim ot) outTy `or`
       let dim = case dimMode of
                   NDim   -> out_dim+1
                   OneDim -> 1
                   NoDim  -> (-1) in
       arrVariable vr (TArray dim it1)
      )

   shapeType exprTy k =
     case exprTy of
       intTy     | isValid intTy      -> k 1 
       TTuple ls | all isValid ls -> k (length ls)
       _ -> Just$"Invalid type for a *shape*: "++ show exprTy
     where
       isValid (TTuple [])     = True
       isValid t | isIntType t = True
       isValid _               = False

   arrVariable vr (TArray expected_dim expected_elt) =
     (lkup vr $ \ argty -> 
        case argty of
          TArray ndim' elty' ->
            assertTyEq ("Array variable ("++show vr++") element type") elty' expected_elt `or`
            ifCheckDims (assertEq ("Array variable ("++show vr++") dimension") ndim' expected_dim))

   expr msg ex expected =
     assertTyEq msg (recoverExpType env ex) expected
   
   lkup v k =
     case M.lookup v env of
       Just x  -> k x
       Nothing -> Just$ "Unbound variable: "++show v
      
   typeFn1 :: String -> Fun1 Exp -> (Type,Type,Maybe ErrorMessage)
   typeFn1 msg (Lam1 (vr,inTy) exp) =
     let env' = M.insert vr inTy env
         ty'  = recoverExpType env' exp 
         err1 = case M.lookup vr env of
                Just _  -> Just (msg++": Local formal param is not globally unique: "++show vr) 
                Nothing -> Nothing
     in (inTy, ty',
         err1 `or` doE env' exp)

   -- TODO: factor these into one variant that takes a list of formals:
   typeFn2 :: String -> Fun2 Exp -> (Type,Type,Type,Maybe ErrorMessage)
   typeFn2 msg (Lam2 (vr1,inTy1) (vr2,inTy2) bod) =
     let env' = M.insert vr1 inTy1 $
                M.insert vr2 inTy2 env
         ty'  = recoverExpType env' bod
         err1 = case M.lookup vr1 env of
                Just _  -> Just (msg++": Local formal param is not globally unique: "++show vr1) 
                Nothing -> Nothing
         err2 = case M.lookup vr2 env of
                Just _  -> Just (msg++": Local formal param is not globally unique: "++show vr2) 
                Nothing -> Nothing                
     in (inTy1, inTy2, ty',
         err1 `or` err2 `or` doE env' bod)

   assertEq :: (Eq a, Show a) => String -> a -> a -> Maybe String
   assertEq msg got expected =
     if got == expected
     then Nothing
     else Just$ mismatchErr msg got expected

   assertTyEq = assertTyEqual dimMode


-- doFn1  mp = doE exp mp 

-- doFn2 :: Fun2 Exp -> UseMap -> UseMap
-- doFn2 (Lam2 _ _ exp) mp = doE exp mp 


-- TODO -- need to replace "recoverExpType" with something that will NOT throw a
-- Haskell error.
doE _ _ = Nothing

-------------------------------------------------------------------------------

-- Concatenate error messages:
or :: Maybe ErrorMessage -> Maybe ErrorMessage -> Maybe ErrorMessage 
or (Just x) (Just y) = Just (x++"\n"++y)
or (Just x) Nothing = Just x
or Nothing (Just x) = Just x
or Nothing Nothing  = Nothing

(?) :: Bool -> ErrorMessage -> Maybe ErrorMessage
True ? m  = Just m
False ? _ = Nothing
