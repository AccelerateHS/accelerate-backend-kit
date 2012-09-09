{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | In the process of Accelerate AST simplification, we don't go
-- straight from Data.Array.Accelerate.AST to the final SimpleAST.
-- Rather, there are intermediate steps.  This module contains
-- intermediate representation(s) used by other passes found in this
-- directory.

module Data.Array.Accelerate.SimplePasses.IRTypes
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

import Data.Array.Accelerate.SimpleAST hiding (Exp(..), AExp(..))
import qualified Data.Array.Accelerate.SimpleAST as S

--------------------------------------------------------------------------------


-- | Array-level expressions.  
-- 
--   This is an intermediate datatype that is isomorphic to the the
--   Accelerate frontend AST type ("Data.Array.Accelerate.AST")
--   enabling direct translation.  It is also used as the IR for
--   subsequent lowerings (e.g. staticTuples or liftComplexRands).
-- 
--   See documentation for SimpleAST.  Not reproducing it here.
--   This type differs by including ArrayTuple, TupleRefFromRight, and Apply.
-- 
--   This type is parameterized by an arbitrary annotation, which
--   usually includes the type.
data AExp a = 
    ArrayTuple a [AExp a]           -- Tuple of arrays.
  | TupleRefFromRight a Int (AExp a)  -- Dereference tuple 
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
--   This differs from `SimpleAST` in that it includes dynamic
--   list-like treatment of indices.
-- 
data Exp =
  -- All four of the following forms evaluate to an "Index":
    EIndex [Exp] -- An index into a multi-dimensional array:
  | EIndexConsDynamic Exp Exp -- Add to the front of an index expression.
  | EIndexHeadDynamic Exp     -- Project just the first dimension of an index.
  | EIndexTailDynamic Exp     -- Retain all dimensions but the first.
  -----------------------------------
  | ETuple [Exp]            -- Build a tuple.
  | ETupProject Int Int Exp -- Project a consecutive series of fields from a tuple.
  | EVr Var
  | ELet (Var,Type,Exp) Exp
  | EPrimApp Type Prim [Exp]
  | EConst Const
  | ECond Exp Exp Exp
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
-- final SimpleAST type.
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
    EShapeSize ex            -> S.EShapeSize (f ex)         
    EPrimApp ty p es         -> S.EPrimApp ty p (L.map f es)
    ETupProject ind len ex   -> S.ETupProject ind len (f ex)
    EIndex indls             -> S.EIndex (L.map f indls)
    EIndexScalar (Vr _ v) ex -> S.EIndexScalar v (f ex)
    EShape (Vr _ v)          -> S.EShape v
    EIndexScalar ae _ -> error$"IRTypes.convertExps: expected EIndexScalar to have plain variable as array input, found: "++show ae
    EShape       ae   -> error$"IRTypes.convertExps: expected EShape" ++ " to have plain variable as array input, found: "++show ae

    EIndexConsDynamic e1 e2 -> error "dynamic index manipulation not permitted in final SimpleAST"
    EIndexHeadDynamic ex    -> error "dynamic index manipulation not permitted in final SimpleAST"
    EIndexTailDynamic ex    -> error "dynamic index manipulation not permitted in final SimpleAST"

convertFun1 :: S.Fun1 Exp -> S.Fun1 S.Exp
convertFun1 (Lam1 bnd bod) = Lam1 bnd $ convertExps bod

convertFun2 :: S.Fun2 Exp -> S.Fun2 S.Exp
convertFun2 (Lam2 bnd1 bnd2 bod) = Lam2 bnd1 bnd2 $ convertExps bod

-- | Convert Array expressions /that meet the restrictions/ to the
--   final SimpleAST type.
convertAExps :: AExp Type -> S.AExp
convertAExps aex =
  let cE  = convertExps 
      cF  = convertFun1
      cF2 = convertFun2
      f   = convertAExps
  in
  case aex of 
     Cond _ a (Vr _ v1) (Vr _ v2) -> S.Cond (cE a) v1 v2
     Unit _ ex                   -> S.Unit (cE ex)
     Use ty arr                  -> S.Use ty arr
     Generate aty ex fn          -> S.Generate aty (cE ex) (cF fn)
     ZipWith _ fn (Vr _ v1) (Vr _ v2) -> S.ZipWith (cF2 fn) v1 v2 
     Map     _ fn (Vr _ v)       -> S.Map     (cF fn)  v
     Replicate aty slice ex (Vr _ v) -> S.Replicate aty slice (cE ex) v
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
     TupleRefFromRight _ _ _ -> error$"convertAExps: input doesn't meet constraints, TupleRefFromRight encountered."
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
     TupleRefFromRight a _ _     -> a


-- TEMP: shouldn't need this:
reverseConvertExps :: S.Exp -> Exp
reverseConvertExps expr = 
  let f = reverseConvertExps 
      dt = TTuple [] -- Dummy type
  in
  case expr of 
    S.EVr  v                -> EVr  v
    S.ELet (vr,_ty,lhs) bod -> ELet (vr, _ty, f lhs) (f bod)
    S.ETuple es             -> ETuple (L.map f es)
    S.EConst c              -> EConst c              
    S.ECond e1 e2 e3        -> ECond (f e1) (f e2) (f e3)
    S.EIndexScalar v ex     -> EIndexScalar (Vr dt v) (f ex)
    S.EShape v              -> EShape (Vr dt v)
    S.EShapeSize ex         -> EShapeSize (f ex)         
    S.EPrimApp ty p es      -> EPrimApp ty p (L.map f es)
    S.ETupProject ind len ex -> ETupProject ind len (f ex)
    S.EIndex indls          -> EIndex (L.map f indls)

reverseConvertFun1 :: S.Fun1 S.Exp -> S.Fun1 Exp
reverseConvertFun1 (S.Lam1 bnd bod) = Lam1 bnd $ reverseConvertExps bod

reverseConvertFun2 :: S.Fun2 S.Exp -> S.Fun2 Exp 
reverseConvertFun2 (S.Lam2 bnd1 bnd2 bod) = Lam2 bnd1 bnd2 $ reverseConvertExps bod

-- TEMPORARY! -- THIS PUTS IN NONSENSE TYPES!
reverseConvertAExps :: S.AExp -> AExp Type
reverseConvertAExps aex =
  let cE  = reverseConvertExps
      cF  = reverseConvertFun1
      cF2 = reverseConvertFun2
      f   = reverseConvertAExps
      dt  = TTuple [] -- Dummy type
  in
  case aex of 
--     S.Vr v                      -> Vr dt v
--     S.Let (v,ty,lhs) bod        -> Let dt (v,ty, f lhs) (f bod)
     S.Cond a b c                -> Cond dt (cE a) (Vr dt b) (Vr dt c)
     S.Unit ex                   -> Unit dt (cE ex)
     S.Use ty arr                -> Use ty arr
     S.Generate aty ex fn        -> Generate aty (cE ex) (cF fn)
     S.ZipWith fn v1 v2          -> ZipWith dt (cF2 fn) (Vr dt v1) (Vr dt v2)
     S.Map     fn v              -> Map     dt (cF fn)  (Vr dt v)
     S.Replicate aty slice ex v  -> Replicate aty slice (cE ex) (Vr dt v)
     S.Index     slc v     ex    -> Index dt slc (Vr dt v) (cE ex)
     S.Fold  fn einit (v)        -> Fold     dt (cF2 fn) (cE einit) (Vr dt v)
     S.Fold1 fn       (v)        -> Fold1    dt (cF2 fn)            (Vr dt v)
     S.FoldSeg fn einit (v) (v2) -> FoldSeg  dt (cF2 fn) (cE einit) (Vr dt v) (Vr dt v2)
     S.Fold1Seg fn      (v) (v2) -> Fold1Seg dt (cF2 fn)            (Vr dt v) (Vr dt v2)
     S.Scanl    fn einit (v)     -> Scanl    dt (cF2 fn) (cE einit) (Vr dt v)
     S.Scanl'   fn einit (v)     -> Scanl'   dt (cF2 fn) (cE einit) (Vr dt v)
     S.Scanl1   fn       (v)     -> Scanl1   dt (cF2 fn)            (Vr dt v)
     S.Scanr    fn einit (v)     -> Scanr    dt (cF2 fn) (cE einit) (Vr dt v)
     S.Scanr'   fn einit (v)     -> Scanr'   dt (cF2 fn) (cE einit) (Vr dt v)
     S.Scanr1   fn       (v)     -> Scanr1   dt (cF2 fn)            (Vr dt v)
     S.Permute fn2 (v) fn1 (v2)  -> Permute  dt (cF2 fn2) (Vr dt v) (cF fn1) (Vr dt v2)
     S.Backpermute ex fn  (v)    -> Backpermute dt (cE ex) (cF fn) (Vr dt v)
     S.Reshape     ex     (v)    -> Reshape     dt (cE ex)         (Vr dt v)
     S.Stencil   fn bndry (v)    -> Stencil     dt (cF fn) bndry   (Vr dt v)
     S.Stencil2  fn bnd1 v bnd2 v2 -> Stencil2 dt (cF2 fn) bnd1 (Vr dt v) bnd2 (Vr dt v2)
