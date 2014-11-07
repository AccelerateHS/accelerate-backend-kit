{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | In the process of Accelerate AST simplification, we don't go
-- straight from Data.Array.Accelerate.AST to the SimpleAcc AST.
-- Rather, there are intermediate steps.  This module contains
-- intermediate representation(s) used by other passes in the compiler
-- but NOT exported for external consumption.
--
-- In particular this module contains an isomorphic representation of
-- Accelerate's internal IR that is NOT flattened into a `Prog` type.

module Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone
   (
     -- * Intermediate representations.
     AExp(..), getAnnot,
     Exp(..), -- Fun1(..), Fun2(..),
     convertAExps,
     convertExps,
     convertFun1, convertFun2,

     -- reverseConvertExps, reverseConvertFun1, reverseConvertFun2, reverseConvertAExps -- TEMP

   )
       where

import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import           System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map  as M
import qualified Data.List as L

import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc hiding (Exp(..), AExp(..))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S

--------------------------------------------------------------------------------


-- | Array-level expressions.
--
--   This is an intermediate datatype that is isomorphic to the the
--   Accelerate frontend AST type ("Data.Array.Accelerate.AST")
--   enabling direct translation.  It is also used as the IR for
--   subsequent lowerings (e.g. staticTuples or liftComplexRands).
--
--   See documentation for SimpleAcc AST.  Not reproducing it here.
--   This type differs by including ArrayTuple, TupleRefFromRight, and Apply.
--
--   This type is parameterized by an arbitrary annotation, which
--   usually includes the type.
data AExp a =
    ArrayTuple a [AExp a]           -- Tuple of arrays.
  -- attempt same approach as with ETuples here
  -- That is: Project a consecutive series of fields from a tuple.
  | TupleRefFromRight a Int Int (AExp a)  -- Dereference tuple
  | Apply a (Fun1 (AExp a)) (AExp a)      -- Apply a known array-level function.
  ------------------------------
  | Vr   a Var
  | Unit a Exp
  | Let  a (Var,Type,(AExp a)) (AExp a)
  | Cond a Exp (AExp a) (AExp a)
  | Use  a AccArray
  | Generate  a Exp (Fun1 Exp)
  | Replicate a SliceType Exp (AExp a)
  | Index     a SliceType (AExp a) Exp
  | Map       a (Fun1 Exp) (AExp a)
  | ZipWith   a (Fun2 Exp) (AExp a) (AExp a)
  | Fold      a (Fun2 Exp) Exp (AExp a)
  | Fold1     a (Fun2 Exp) (AExp a)
  | FoldSeg   a (Fun2 Exp) Exp (AExp a) (AExp a)
  | Fold1Seg  a (Fun2 Exp)     (AExp a) (AExp a)
  | Scanl     a (Fun2 Exp) Exp (AExp a)
  | Scanl'    a (Fun2 Exp) Exp (AExp a)
  | Scanl1    a (Fun2 Exp)     (AExp a)
  | Scanr     a (Fun2 Exp) Exp (AExp a)
  | Scanr'    a (Fun2 Exp) Exp (AExp a)
  | Scanr1    a (Fun2 Exp)     (AExp a)
  | Permute   a (Fun2 Exp) (AExp a) (Fun1 Exp) (AExp a)
  | Backpermute a Exp (Fun1 Exp) (AExp a)
  | Reshape     a Exp      (AExp a)
  | Stencil     a (Fun1 Exp) Boundary (AExp a)
  | Stencil2    a (Fun2 Exp) Boundary (AExp a) Boundary (AExp a)
 deriving (Read,Show,Eq,Generic)

--------------------------------------------------------------------------------
-- Scalar Expressions
--------------------------------------------------------------------------------

-- | Scalar expressions
--
--   This differs from `SimpleAcc` in that it includes dynamic
--   list-like treatment of indices.
--
data Exp =
  -- All six of the following forms evaluate to an "Index":
    EIndex [Exp] -- An index into a multi-dimensional array:
  | EIndexConsDynamic Exp Exp -- Add to the front of an index expression.
  | EIndexHeadDynamic Exp     -- Project just the first dimension of an index.
  | EIndexTailDynamic Exp     -- Retain all dimensions but the first.
  -----------------------------------
  | ETuple [Exp]            -- Build a tuple.  Stored in REVERSE of textual order in the IR.
  | ETupProject Int Int Exp -- Project a consecutive series of fields from a tuple.
  | EVr Var
  | ELet (Var,Type,Exp) Exp
  | EPrimApp Type Prim [Exp]
  | EConst Const
  | ECond Exp Exp Exp
  | EWhile (Fun1 Exp) (Fun1 Exp) Exp
  | EIndexScalar (AExp Type) Exp
  | EShape (AExp Type)
  | EShapeSize Exp
 deriving (Read,Show,Eq,Generic)

--------------------------------------------------------------------------------

-- instance Out (Fun1 (AExp Type))
instance Out a => Out (Fun1 (AExp a))
instance Out (Fun1 Exp)
instance Out (Fun2 Exp)
instance Out Exp
instance Out a => Out (AExp a)
-- instance Out (AExp Type)
-- instance Out AFun

--------------------------------------------------------------------------------
-- Conversion functions
--------------------------------------------------------------------------------

-- | Convert scalar expressions /that meet the restrictions/ to the
-- final SimpleAcc type.
convertExps :: Exp -> S.Exp
convertExps expr =
  let f = convertExps in
  case expr of
    -- Good old boilerplate:
    EVr  v                   -> S.EVr  v
    ELet (vr,_ty,lhs) bod    -> S.ELet (vr, _ty, f lhs) (f bod)
    ETuple es                -> S.ETuple (L.map f es)
    EConst c                 -> S.EConst c
    ECond e1 e2 e3           -> S.ECond (f e1) (f e2) (f e3)
    EWhile f1 f2 e3          -> S.EWhile (convertFun1 f1) (convertFun1 f2) (f e3)
    EShapeSize ex            -> S.EShapeSize (f ex)
    EPrimApp ty p es         -> S.EPrimApp ty p (L.map f es)
    ETupProject ind len ex   -> S.ETupProject ind len (f ex)
    EIndex indls             -> S.EIndex (L.map f indls)
    EIndexScalar (Vr _ v) ex -> S.EIndexScalar v (f ex)
    EShape (Vr _ v)          -> S.EShape v
    EIndexScalar ae _        -> error $ "AccClone.convertExps: expected EIndexScalar to have plain variable as array input, found: "++show ae
    EShape       ae          -> error $ "AccClone.convertExps: expected EShape" ++ " to have plain variable as array input, found: "++show ae

    EIndexConsDynamic _e1 _e2 -> error "dynamic index manipulation not permitted in SimpleAcc IR"
    EIndexHeadDynamic _ex    -> error "dynamic index manipulation not permitted in SimpleAcc IR"
    EIndexTailDynamic _ex    -> error "dynamic index manipulation not permitted in SimpleAcc IR"

convertFun1 :: S.Fun1 Exp -> S.Fun1 S.Exp
convertFun1 (Lam1 bnd bod) = Lam1 bnd $ convertExps bod

convertFun2 :: S.Fun2 Exp -> S.Fun2 S.Exp
convertFun2 (Lam2 bnd1 bnd2 bod) = Lam2 bnd1 bnd2 $ convertExps bod

-- | Convert Array expressions /that meet the restrictions/ to the
--   final SimpleAcc AST type.
convertAExps :: AExp Type -> S.AExp
convertAExps aex =
  let cE  = convertExps
      cF  = convertFun1
      cF2 = convertFun2
  in
  case aex of
     Cond _ a (Vr _ v1) (Vr _ v2) -> S.Cond (cE a) v1 v2
     Unit _ ex                    -> S.Unit (cE ex)
     Use _ arr                    -> S.Use arr
     Generate _ ex fn             -> S.Generate (cE ex) (cF fn)
     ZipWith _ fn (Vr _ v1) (Vr _ v2) -> S.ZipWith (cF2 fn) v1 v2
     Map     _ fn (Vr _ v)            -> S.Map     (cF fn)  v
     Replicate _aty slice ex (Vr _ v) -> S.Replicate slice (cE ex) v
     Index     _ slc (Vr _ v)    ex    -> S.Index slc v (cE ex)
     Fold  _ fn einit (Vr _ v)         -> S.Fold     (cF2 fn) (cE einit) v
     Fold1 _ fn       (Vr _ v)         -> S.Fold1    (cF2 fn)            v
     FoldSeg _ fn einit (Vr _ v) (Vr _ v2) -> S.FoldSeg  (cF2 fn) (cE einit) v v2
     Fold1Seg _ fn      (Vr _ v) (Vr _ v2) -> S.Fold1Seg (cF2 fn)            v v2
     Scanl    _ fn einit (Vr _ v)      -> S.Scanl    (cF2 fn) (cE einit) v
     Scanl'   _ fn einit (Vr _ v)      -> S.Scanl'   (cF2 fn) (cE einit) v
     Scanl1   _ fn       (Vr _ v)      -> S.Scanl1   (cF2 fn)            v
     Scanr    _ fn einit (Vr _ v)      -> S.Scanr    (cF2 fn) (cE einit) v
     Scanr'   _ fn einit (Vr _ v)      -> S.Scanr'   (cF2 fn) (cE einit) v
     Scanr1   _ fn       (Vr _ v)      -> S.Scanr1   (cF2 fn)            v
     Permute _ fn2 (Vr _ v1) fn1 (Vr _ v2)   -> S.Permute (cF2 fn2) v1 (cF fn1) v2
     Backpermute _ ex fn  (Vr _ v)     -> S.Backpermute (cE ex) (cF fn) v
     Reshape     _ ex     (Vr _ v)     -> S.Reshape     (cE ex)         v
     Stencil   _ fn bndry (Vr _ v)     -> S.Stencil     (cF fn) bndry   v
     Stencil2  _ fn bnd1 (Vr _ v1) bnd2 (Vr _ v2) -> S.Stencil2 (cF2 fn) bnd1 v1 bnd2 v2
     Vr _ _                  -> error$"convertAExps: input doesn't meet constraints, Vr encountered."
     Let _ _ _               -> error$"convertAExps: input doesn't meet constraints, Let encountered."
     Apply _ _ _             -> error$"convertAExps: input doesn't meet constraints, Apply encountered."
     ArrayTuple _  _         -> error$"convertAExps: input doesn't meet constraints, ArrayTuple encountered."
     TupleRefFromRight _ _ _ _ -> error$"convertAExps: input doesn't meet constraints, TupleRefFromRight encountered."
     oth -> error$"convertAExps: invariants not matched: "++show oth

-- | Extract the annotation component from an AExp:
getAnnot :: AExp a -> a
getAnnot ae =
  case ae of
     Vr a _                      -> a
     Let a _ _                   -> a
     Cond a _ _ _                -> a
     Unit a _                    -> a
     Use a _                     -> a
     Generate a _ _              -> a
     ZipWith a _ _ _             -> a
     Map     a _ _               -> a
     Replicate a _ _ _           -> a
     Index     a _ _ _           -> a
     Fold      a _ _ _           -> a
     Fold1     a _ _             -> a
     FoldSeg   a _ _ _ _         -> a
     Fold1Seg  a _ _ _           -> a
     Scanl     a _ _ _           -> a
     Scanl'    a _ _ _           -> a
     Scanl1    a   _ _           -> a
     Scanr     a _ _ _           -> a
     Scanr'    a _ _ _           -> a
     Scanr1    a   _ _           -> a
     Permute   a _ _ _ _         -> a
     Backpermute a _ _ _         -> a
     Reshape     a _ _           -> a
     Stencil     a _ _ _         -> a
     Stencil2    a _ _ _ _ _     -> a
     Apply       a _ _           -> a
     ArrayTuple  a _             -> a
     TupleRefFromRight a _ _ _   -> a

