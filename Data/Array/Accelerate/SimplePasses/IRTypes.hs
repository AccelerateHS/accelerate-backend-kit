{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | We don't go straight from Data.Array.Accelerate.AST to the SimpleAST.
--   This file contains intermediate representation(s).

module Data.Array.Accelerate.SimplePasses.IRTypes
   (
     AExp(..), 
     Exp(..), -- Fun1(..), Fun2(..),
     convertAExps,
     convertExps, 
     convertFun1, convertFun2,
                  
     reverseConvertExps, reverseConvertFun1, reverseConvertFun2, reverseConvertAExps -- TEMP                  
                  
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
--   subsequent lowerings ("Data.Array.Accelerate.SimplePasses.Lowering").
-- 
--   See documentation for SimpleAST.  Not reproducing it here.
--   This type differs by including ArrayTuple, TupleRefFromRight, and Apply.
-- 
data AExp = 
    ArrayTuple [AExp]           -- Tuple of arrays.
  | TupleRefFromRight Int AExp  -- Dereference tuple 
  | Apply (Fun1 AExp) AExp      -- Apply a known array-level function.
  ------------------------------  
  | Vr Var
  | Unit Exp
  | Let (Var,Type,AExp) AExp
  | Cond Exp AExp AExp
  | Use       Type AccArray
  | Generate  Type Exp (Fun1 Exp)
  | Replicate Type SliceType Exp AExp
  | Index     SliceType AExp Exp 
  | Map      (Fun1 Exp) AExp
  | ZipWith  (Fun2 Exp) AExp AExp
  | Fold     (Fun2 Exp) Exp AExp 
  | Fold1    (Fun2 Exp) AExp     
  | FoldSeg  (Fun2 Exp) Exp AExp AExp
  | Fold1Seg (Fun2 Exp)     AExp AExp
  | Scanl    (Fun2 Exp) Exp AExp     
  | Scanl'   (Fun2 Exp) Exp AExp      
  | Scanl1   (Fun2 Exp)     AExp     
  | Scanr    (Fun2 Exp) Exp AExp    
  | Scanr'   (Fun2 Exp) Exp AExp   
  | Scanr1   (Fun2 Exp)     AExp  
  | Permute  (Fun2 Exp) AExp (Fun1 Exp) AExp 
  | Backpermute Exp (Fun1 Exp) AExp   
  | Reshape     Exp      AExp   
  | Stencil  (Fun1 Exp) Boundary AExp
  | Stencil2 (Fun2 Exp) Boundary AExp Boundary AExp 
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
    EIndex [Exp] -- An index into a multi-dimensional array:
  | EIndexConsDynamic Exp Exp
  | EIndexHeadDynamic Exp 
  | EIndexTailDynamic Exp   
--  | EIndexAny    
  -----------------------------------
  | EVr Var
  | ELet (Var,Type,Exp) Exp
  | EPrimApp Type Prim [Exp]
  | ETuple [Exp]
  | EConst Const
  | ETupProjectFromRight Int Exp
  | ECond Exp Exp Exp
  | EIndexScalar AExp Exp 
  | EShape AExp
  | EShapeSize Exp 
 deriving (Read,Show,Eq,Generic)

--------------------------------------------------------------------------------

instance Out (Fun1 AExp)
instance Out (Fun1 Exp)
instance Out (Fun2 Exp)
instance Out Exp
instance Out AExp
-- instance Out AFun

--------------------------------------------------------------------------------
-- Conversion functions
--------------------------------------------------------------------------------

convertExps :: Exp -> S.Exp
convertExps expr = 
  let f = convertExps in
  case expr of 
    EVr  v                -> S.EVr  v
    ELet (vr,_ty,lhs) bod -> S.ELet (vr, _ty, f lhs) (f bod)
    ETuple es             -> S.ETuple (L.map f es)
    EConst c              -> S.EConst c              
    ECond e1 e2 e3        -> S.ECond (f e1) (f e2) (f e3)
    EIndexScalar ae ex    -> S.EIndexScalar (convertAExps ae) (f ex)
    EShape ae             -> S.EShape (convertAExps ae)
    EShapeSize ex         -> S.EShapeSize (f ex)         
    EPrimApp ty p es      -> S.EPrimApp ty p (L.map f es)
    ETupProjectFromRight ind ex -> S.ETupProjectFromRight ind (f ex)
    EIndex indls            -> S.EIndex (L.map f indls)
    EIndexConsDynamic e1 e2 -> S.EIndexConsDynamic (f e1) (f e2)
    EIndexHeadDynamic ex    -> S.EIndexHeadDynamic (f ex)
    EIndexTailDynamic ex    -> S.EIndexTailDynamic (f ex)
    
convertFun1 :: S.Fun1 Exp -> S.Fun1 S.Exp
convertFun1 (Lam1 bnd bod) = Lam1 bnd $ convertExps bod

convertFun2 :: S.Fun2 Exp -> S.Fun2 S.Exp
convertFun2 (Lam2 bnd1 bnd2 bod) = Lam2 bnd1 bnd2 $ convertExps bod

-- | Convert Array expressions /that meet the restrictions/ to the
--   final SimpleAST type.
convertAExps :: AExp -> S.AExp
convertAExps aex =
  let cE  = convertExps 
      cF  = convertFun1
      cF2 = convertFun2
      f   = convertAExps
  in
  case aex of 
     Vr v                      -> S.Vr v
     Let (v,ty,lhs) bod        -> S.Let (v,ty, f lhs) (f bod)
     Cond a b c                -> S.Cond (cE a) (f b) (f c)
     Unit ex                   -> S.Unit (cE ex)
     Use ty arr                -> S.Use ty arr
     Generate aty ex fn        -> S.Generate aty (cE ex) (cF fn)
     ZipWith fn ae1 ae2        -> S.ZipWith (cF2 fn) (f ae1) (f ae2)
     Map     fn ae             -> S.Map     (cF fn)  (f ae)
     Replicate aty slice ex ae -> S.Replicate aty slice (cE ex) (f ae)
     Index     slc ae    ex    -> S.Index slc (f ae) (cE ex)
     Fold  fn einit ae         -> S.Fold     (cF2 fn) (cE einit) (f ae)
     Fold1 fn       ae         -> S.Fold1    (cF2 fn)            (f ae)
     FoldSeg fn einit ae aeseg -> S.FoldSeg  (cF2 fn) (cE einit) (f ae) (f aeseg)
     Fold1Seg fn      ae aeseg -> S.Fold1Seg (cF2 fn)            (f ae) (f aeseg)
     Scanl    fn einit ae      -> S.Scanl    (cF2 fn) (cE einit) (f ae)
     Scanl'   fn einit ae      -> S.Scanl'   (cF2 fn) (cE einit) (f ae)
     Scanl1   fn       ae      -> S.Scanl1   (cF2 fn)            (f ae)
     Scanr    fn einit ae      -> S.Scanr    (cF2 fn) (cE einit) (f ae)
     Scanr'   fn einit ae      -> S.Scanr'   (cF2 fn) (cE einit) (f ae)
     Scanr1   fn       ae      -> S.Scanr1   (cF2 fn)            (f ae)
     Permute fn2 ae1 fn1 ae2   -> S.Permute (cF2 fn2) (f ae1) (cF fn1) (f ae2)
     Backpermute ex fn  ae     -> S.Backpermute (cE ex) (cF fn) (f ae)
     Reshape     ex     ae     -> S.Reshape     (cE ex)         (f ae)
     Stencil   fn bndry ae     -> S.Stencil     (cF fn) bndry   (f ae)
     Stencil2  fn bnd1 ae1 bnd2 ae2 -> S.Stencil2 (cF2 fn) bnd1 (f ae1) bnd2 (f ae2)
     Apply _ _             -> error$"convertAExps: input doesn't meet constraints, Apply encountered."
     ArrayTuple _          -> error$"convertAExps: input doesn't meet constraints, ArrayTuple encountered."
     TupleRefFromRight _ _ -> error$"convertAExps: input doesn't meet constraints, TupleRefFromRight encountered."


-- TEMP: shouldn't need this:
reverseConvertExps :: S.Exp -> Exp
reverseConvertExps expr = 
  let f = reverseConvertExps in
  case expr of 
    S.EVr  v                -> EVr  v
    S.ELet (vr,_ty,lhs) bod -> ELet (vr, _ty, f lhs) (f bod)
    S.ETuple es             -> ETuple (L.map f es)
    S.EConst c              -> EConst c              
    S.ECond e1 e2 e3        -> ECond (f e1) (f e2) (f e3)
    S.EIndexScalar ae ex    -> EIndexScalar (reverseConvertAExps ae) (f ex)
    S.EShape ae             -> EShape (reverseConvertAExps ae)
    S.EShapeSize ex         -> EShapeSize (f ex)         
    S.EPrimApp ty p es      -> EPrimApp ty p (L.map f es)
    S.ETupProjectFromRight ind ex -> ETupProjectFromRight ind (f ex)
    S.EIndex indls          -> EIndex (L.map f indls)
    S.EIndexConsDynamic e1 e2 -> EIndexConsDynamic (f e1) (f e2)
    S.EIndexHeadDynamic ex    -> EIndexHeadDynamic (f ex)
    S.EIndexTailDynamic ex    -> EIndexTailDynamic (f ex)



reverseConvertFun1 :: S.Fun1 S.Exp -> S.Fun1 Exp
reverseConvertFun1 (S.Lam1 bnd bod) = Lam1 bnd $ reverseConvertExps bod

reverseConvertFun2 :: S.Fun2 S.Exp -> S.Fun2 Exp 
reverseConvertFun2 (S.Lam2 bnd1 bnd2 bod) = Lam2 bnd1 bnd2 $ reverseConvertExps bod

-- TEMPORARY!
reverseConvertAExps :: S.AExp -> AExp
reverseConvertAExps aex =
  let cE  = reverseConvertExps
      cF  = reverseConvertFun1
      cF2 = reverseConvertFun2
      f   = reverseConvertAExps
  in
  case aex of 
     S.Vr v                      -> Vr v
     S.Let (v,ty,lhs) bod        -> Let (v,ty, f lhs) (f bod)
     S.Cond a b c                -> Cond (cE a) (f b) (f c)
     S.Unit ex                   -> Unit (cE ex)
     S.Use ty arr                -> Use ty arr
     S.Generate aty ex fn        -> Generate aty (cE ex) (cF fn)
     S.ZipWith fn ae1 ae2        -> ZipWith (cF2 fn) (f ae1) (f ae2)
     S.Map     fn ae             -> Map     (cF fn)  (f ae)
     S.Replicate aty slice ex ae -> Replicate aty slice (cE ex) (f ae)
     S.Index     slc ae    ex    -> Index slc (f ae) (cE ex)
     S.Fold  fn einit ae         -> Fold     (cF2 fn) (cE einit) (f ae)
     S.Fold1 fn       ae         -> Fold1    (cF2 fn)            (f ae)
     S.FoldSeg fn einit ae aeseg -> FoldSeg  (cF2 fn) (cE einit) (f ae) (f aeseg)
     S.Fold1Seg fn      ae aeseg -> Fold1Seg (cF2 fn)            (f ae) (f aeseg)
     S.Scanl    fn einit ae      -> Scanl    (cF2 fn) (cE einit) (f ae)
     S.Scanl'   fn einit ae      -> Scanl'   (cF2 fn) (cE einit) (f ae)
     S.Scanl1   fn       ae      -> Scanl1   (cF2 fn)            (f ae)
     S.Scanr    fn einit ae      -> Scanr    (cF2 fn) (cE einit) (f ae)
     S.Scanr'   fn einit ae      -> Scanr'   (cF2 fn) (cE einit) (f ae)
     S.Scanr1   fn       ae      -> Scanr1   (cF2 fn)            (f ae)
     S.Permute fn2 ae1 fn1 ae2   -> Permute (cF2 fn2) (f ae1) (cF fn1) (f ae2)
     S.Backpermute ex fn  ae     -> Backpermute (cE ex) (cF fn) (f ae)
     S.Reshape     ex     ae     -> Reshape     (cE ex)         (f ae)
     S.Stencil   fn bndry ae     -> Stencil     (cF fn) bndry   (f ae)
     S.Stencil2  fn bnd1 ae1 bnd2 ae2 -> Stencil2 (cF2 fn) bnd1 (f ae1) bnd2 (f ae2)
