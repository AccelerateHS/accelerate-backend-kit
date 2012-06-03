{-# LANGUAGE DeriveGeneric #-}

-- | We don't go straight from Data.Array.Accelerate.AST to the SimpleAST.
--   This file contains intermediate representation(s).

module Data.Array.Accelerate.SimplePasses.IRTypes
   (
     AExp(..), AFun(..), 
     Exp(..), Fun1(..), Fun2(..),
     convertAExps, convertExps
   )
       where

import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import           System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map          as M

import Data.Array.Accelerate.SimpleAST hiding (Exp, AExp, Fun1, Fun2, AFun)
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
    
  | Apply AFun AExp              -- Function $ Argument
  | Cond Exp AExp AExp           -- Array level if statements
  | Use       Type AccArray      -- A real live ARRAY goes here!
  | Generate  Type Exp Fun1      -- Generate Function Array, very similar to map
  | Replicate Type SliceType Exp AExp -- Replicate array across one or more dimensions.
  | Index     SliceType AExp Exp -- Index a sub-array (slice).
                                 -- Index sliceIndex Array SliceDims
  | Map      Fun1 AExp           -- Map Function Array
  | ZipWith  Fun2 AExp AExp      -- ZipWith Function Array1 Array2
  | Fold     Fun2 Exp AExp       -- Fold Function Default Array
  | Fold1    Fun2 AExp           -- Fold1 Function Array
  | FoldSeg  Fun2 Exp AExp AExp  -- FoldSeg Function Default Array 'Segment Descriptor'
  | Fold1Seg Fun2     AExp AExp  -- FoldSeg Function         Array 'Segment Descriptor'
  | Scanl    Fun2 Exp AExp       -- Scanl  Function InitialValue LinearArray
  | Scanl'   Fun2 Exp AExp       -- Scanl' Function InitialValue LinearArray
  | Scanl1   Fun2     AExp       -- Scanl  Function              LinearArray
  | Scanr    Fun2 Exp AExp       -- Scanr  Function InitialValue LinearArray
  | Scanr'   Fun2 Exp AExp       -- Scanr' Function InitialValue LinearArray
  | Scanr1   Fun2     AExp       -- Scanr  Function              LinearArray
  | Permute  Fun2 AExp Fun1 AExp -- Permute CombineFun DefaultArr PermFun SourceArray
  | Backpermute Exp Fun1 AExp    -- Backpermute ResultDimension   PermFun SourceArray
  | Reshape     Exp      AExp    -- Reshape Shape Array
  | Stencil  Fun1 Boundary AExp
  | Stencil2 Fun2 Boundary AExp Boundary AExp -- Two source arrays/boundaries
 deriving (Read,Show,Eq,Generic)

-- | Array-level functions.
data AFun = ALam (Var,Type) AExp
 deriving (Read,Show,Eq,Generic)


--------------------------------------------------------------------------------
-- Scalar Expressions and Functions
--------------------------------------------------------------------------------

-- | Scalar functions, arity 1
data Fun1 = Lam1 (Var,Type) Exp
 deriving (Read,Show,Eq,Generic)

-- | Scalar functions, arity 2
data Fun2 = Lam2 (Var,Type) (Var,Type) Exp
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

instance Out Fun1
instance Out Fun2
instance Out Exp
instance Out AExp
instance Out AFun

--------------------------------------------------------------------------------
-- Temporary conversion function
--------------------------------------------------------------------------------


convertAExps :: AExp -> S.AExp
convertAExps = undefined

convertExps :: Exp -> S.Exp
convertExps = undefined
