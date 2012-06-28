{-# LANGUAGE DeriveGeneric, CPP #-}

module Data.Array.Accelerate.FinalAST 
       (Block(..), Exp(..))
       where

import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import qualified Data.Array.Accelerate.SimpleAST as S

-- | A block of statements representing scalar computation.
data Block = 
    BBlock [(S.Var, S.Type, Exp)] [Exp] -- A series of bindings and then a final return value.
  | BCond S.Var Block Block             -- Conditional execution with nested lexical scopes.
 deriving (Read,Show,Eq,Generic)

-- | Scalar expressions
data Exp =  
    EConst   S.Const             -- Constant.        
  | EVr      S.Var               -- Variable reference.
  | ECond    S.Var  Exp Exp      -- Conditional expression.
  | EPrimApp S.Type S.Prim [Exp] -- Apply a primitive scalar function, includes type of return value.
  | EIndexScalar S.Var [Exp]     -- Project a single scalar from an array variable, takes index argument(s).
  | EProjFromShape Int S.Var     -- Get ONE component of the shape of an Array variable.
 deriving (Read,Show,Eq,Generic)
          
-- That should be about what we need for maximally convenient conversion to C.
















--------------------------------------------------------------------------------
-- Here we sketch it out in steps:

-- STEP 0 : STARTING POINT:
#if 0
-- | Scalar expressions
data Exp = 
    EConst Const              -- Constant.        
  | EVr Var                   -- Variable bound by a Let.
  | ELet (Var,Type,Exp) Exp   -- @ELet var type rhs body@,
                              -- used for common subexpression elimination
  | EPrimApp Type Prim [Exp]  -- *Any* primitive scalar function, including type of return value.
  | ECond Exp Exp Exp         -- Conditional expression (non-strict in 2nd and 3rd argument).
  | EIndexScalar Var Exp      -- Project a single scalar from an array [variable],
                              -- the array expression can not contain any free scalar variables.
  | EShape Var                -- Get the shape of an Array [variable].
  | EShapeSize Exp            -- Number of elements of a shape
  | EIndex [Exp]              -- An index into a multi-dimensional array.
  | ETuple [Exp]              -- Build a tuple.
  | ETupProject {             -- Project a consecutive series of fields from a tuple.
      indexFromRight :: Int , --  * where to start the slice
      len            :: Int , --  * how many scalars to extract
      tupexpr        :: Exp }
 deriving (Read,Show,Eq,Generic)
#endif

-- STEP 1 : REMOVE TUPLES, INCLUDING SHAPES:
#if 0
-- | Scalar expressions
data Exp = 
    EConst Const              -- Constant.        
  | EVr Var                   -- Variable bound by a Let.
  | ELet (Var,Type,Exp) Exp   -- @ELet var type rhs body@,
                              -- used for common subexpression elimination
  | EPrimApp Type Prim [Exp]  -- *Any* primitive scalar function, including type of return value.
  | ECond Exp Exp Exp         -- Conditional expression (non-strict in 2nd and 3rd argument).
  
  | EIndexScalar Var [Exp]    -- Project a single scalar from an array [variable],
                              -- the array expression can not contain any free scalar variables.    
  | EProjFromShape Int Var    -- Get ONE component of the shape of an Array variable.
 deriving (Read,Show,Eq,Generic)
#endif

-- STEP 2 : REMOVE LETS
#if 0
-- | Scalar statements
data Stmt = 
  | SLet (Var,Type,Exp)
  | SCond Exp [Stmt] [Stmt]
  | SReturn Exp
 deriving (Read,Show,Eq,Generic)
#endif
