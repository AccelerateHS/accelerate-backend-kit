{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | We don't go straight from Data.Array.Accelerate.AST to the SimpleAST.
--   This file contains intermediate representation(s).

module Data.Array.Accelerate.SimplePasses.IRTypes
   (
     AExp(..), -- AFun(..), 
     Exp(..), Fun1(..), Fun2(..),
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

import Data.Array.Accelerate.SimpleAST hiding (Exp(..), AExp(..), Fun1(..), Fun2(..), AFun)
import qualified Data.Array.Accelerate.SimpleAST as S

--------------------------------------------------------------------------------


-- | Array-level expressions.  
-- 
-- Many of these constructors contain the result type as the first
-- field.  Types on `Let`s are the only really important ones, but the
-- others can reduce headaches when consuming the AST for constructs
-- like Replicate that change the type.
-- 
-- 
data AExp = 
    Vr Var -- Array variable bound by a Let.
  | Unit Exp -- Turn an element into a singleton array
    -- Let is used for common subexpression elimination
  | Let (Var,Type,AExp) AExp    -- Let Var Type RHS Body
  | ArrayTuple [AExp]           -- Tuple of arrays.
  | TupleRefFromRight Int AExp 
    
  | Apply (Fun1 AExp) AExp              -- Function $ Argument
  | Cond Exp AExp AExp           -- Array level if statements
  | Use       Type AccArray      -- A real live ARRAY goes here!
  | Generate  Type Exp (Fun1 Exp)      -- Generate Function Array, very similar to map
  | Replicate Type SliceType Exp AExp -- Replicate array across one or more dimensions.
  | Index     SliceType AExp Exp -- Index a sub-array (slice).
                                 -- Index sliceIndex Array SliceDims
  | Map      (Fun1 Exp) AExp           -- Map Function Array
  | ZipWith  (Fun2 Exp) AExp AExp      -- ZipWith Function Array1 Array2
  | Fold     (Fun2 Exp) Exp AExp       -- Fold Function Default Array
  | Fold1    (Fun2 Exp) AExp           -- Fold1 Function Array
  | FoldSeg  (Fun2 Exp) Exp AExp AExp  -- FoldSeg Function Default Array 'Segment Descriptor'
  | Fold1Seg (Fun2 Exp)     AExp AExp  -- FoldSeg Function         Array 'Segment Descriptor'
  | Scanl    (Fun2 Exp) Exp AExp       -- Scanl  Function InitialValue LinearArray
  | Scanl'   (Fun2 Exp) Exp AExp       -- Scanl' Function InitialValue LinearArray
  | Scanl1   (Fun2 Exp)     AExp       -- Scanl  Function              LinearArray
  | Scanr    (Fun2 Exp) Exp AExp       -- Scanr  Function InitialValue LinearArray
  | Scanr'   (Fun2 Exp) Exp AExp       -- Scanr' Function InitialValue LinearArray
  | Scanr1   (Fun2 Exp)     AExp       -- Scanr  Function              LinearArray
  | Permute  (Fun2 Exp) AExp (Fun1 Exp) AExp -- Permute CombineFun DefaultArr PermFun SourceArray
  | Backpermute Exp (Fun1 Exp) AExp    -- Backpermute ResultDimension   PermFun SourceArray
  | Reshape     Exp      AExp    -- Reshape Shape Array
  | Stencil  (Fun1 Exp) Boundary AExp
  | Stencil2 (Fun2 Exp) Boundary AExp Boundary AExp -- Two source arrays/boundaries
 deriving (Read,Show,Eq,Generic)

-- | Array-level functions.
-- data AFun = ALam (Var,Type) AExp
--  deriving (Read,Show,Eq,Generic)


--------------------------------------------------------------------------------
-- Scalar Expressions and Functions
--------------------------------------------------------------------------------

-- | Scalar functions, arity 1
data Fun1 a = Lam1 (Var,Type) a
 deriving (Read,Show,Eq,Generic)

-- | Scalar functions, arity 2
data Fun2 a = Lam2 (Var,Type) (Var,Type) a
 deriving (Read,Show,Eq,Generic)

-- | Scalar expressions
data Exp = 
    EVr Var -- Variable bound by a Let.
  | ELet (Var,Type,Exp) Exp    -- ELet Var Type RHS Body
  -- ELet is used for common subexpression elimination
  | EPrimApp Type Prim [Exp]  -- *Any* primitive scalar function, including type of return value.
  | ETuple [Exp]
  | EConst Const
   -- [2012.04.02] I can't presently compute the length from the TupleIdx.
   --  | EPrj Int Int Exp  -- n m e : Project the nth field of an m-length tuple.
  | ETupProjectFromRight Int Exp  -- Project the nth field FROM THE RIGHT end of the tuple.  
  | EIndex [Exp] -- An index into a multi-dimensional array:
--  | EIndexAny  
  -- Accelerate allows run-time CONSING of indices:
  -- (In a staged model like this shouldn't we be able to get rid of that at metaprogram eval time?)
  | EIndexConsDynamic Exp Exp
  | EIndexHeadDynamic Exp 
  | EIndexTailDynamic Exp 
   -- Conditional expression (non-strict in 2nd and 3rd argument):
  | ECond Exp Exp Exp
   -- Project a single scalar from an array,
   -- the array expression can not contain any free scalar variables:
  | EIndexScalar AExp Exp 
   -- Get the shape of an Array:
   -- The array expression can not contain any free scalar variables
  | EShape AExp
   -- Number of elements of a shape
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
    
convertFun1 :: Fun1 Exp -> S.Fun1
convertFun1 (Lam1 bnd bod) = S.Lam1 bnd $ convertExps bod

convertFun2 :: Fun2 Exp -> S.Fun2
convertFun2 (Lam2 bnd1 bnd2 bod) = S.Lam2 bnd1 bnd2 $ convertExps bod


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



reverseConvertFun1 :: S.Fun1 -> Fun1 Exp
reverseConvertFun1 (S.Lam1 bnd bod) = Lam1 bnd $ reverseConvertExps bod

reverseConvertFun2 :: S.Fun2 -> Fun2 Exp 
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
