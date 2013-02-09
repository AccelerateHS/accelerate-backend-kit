
{-# LANGUAGE DeriveGeneric #-}

-- | A lower-level intermediate representation that has certain notable differences
-- from Accelerate's front-end representation.  Everything is one dimensional, and
-- there are no tuples at the array or scalar levels.  Accordingly, array operations
-- potentially have more than one output binding, and the lambdas that parameterize
-- them may have more (untupled) arguments than before.  The set of array operators
-- is also greatly reduced.
--
-- Scalar computations explicitly separate statements from expressions, making code
-- generation to C-like languages easy.  
--
-- The language is still purely functional.

module Data.Array.Accelerate.BackendKit.IRs.CLike
       (
         -- * LLIR: modified, lower-level versions of the AST in
         -- "Data.Array.Accelerate.SimpleAST".  Full documentation not
         -- duplicated here.
         LLProg(..), LLProgBind(..), TopLvlForm(..), ScalarBlock(..), Stmt(..), Exp(..),
         Direction(..), Fun(..),

         -- * Helper functions for the LLIR 
         lookupProgBind, expFreeVars, stmtFreeVars, scalarBlockFreeVars
       )
       where

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SA
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Var,Type,Prim,AccArray,TrivialExp)
import           Data.Array.Accelerate.BackendKit.IRs.Metadata   (ArraySizeEstimate)
import           Text.PrettyPrint.GenericPretty (Out, Generic)
import qualified Data.Set  as S
import qualified Data.Map  as M
import           Data.List as L


----------------------------------------------------------------------------------------------------
-- Low Level Intermediate Representation
----------------------------------------------------------------------------------------------------

-- | The Low-Level (C-like) AST.
data LLProg decor = LLProg { 
  progBinds   :: [LLProgBind decor],
  progResults :: [Var],
  uniqueCounter :: Int,
  progType    :: Type, -- Final, pre-flattened type, can be an array-tuple.

  -- | Describes the type and shape of all top level binds.
  --   All arrays are one-dimensional at this point, so size is a scalar.
  --   Scalar variables have entries in this map, but their size is listed as zero.
  sizeEnv :: M.Map Var (Type, TrivialExp)
  
} deriving (Read,Show,Eq,Generic, Ord)

-- | A progbind may bind multiple arrays simultaneously.  The unzipped
-- nature of arrays is exposed directly in the AST at this point.
-- 
-- For example, a Generate parameterized by a ScalarBlock that returns
-- three values will in turn produce three arrays.  All three arrays
-- must be the same shape.
data LLProgBind decor = LLProgBind [(Var,Type)] decor TopLvlForm
    deriving (Read,Show,Eq,Generic, Ord)
  
------------------------------------------------------------
-- Accelerate Array-level Expressions
------------------------------------------------------------

-- A top level operation, including array and scalar expressions.
data TopLvlForm =   
    ScalarCode ScalarBlock -- A block of Scalar code binding one or more variables.
  | Cond Exp Var Var
  | Use       AccArray
  | Generate  ScalarBlock (Fun ScalarBlock)

  | Fold (Fun ScalarBlock) ScalarBlock Var (Maybe Var) -- A possibly segmented fold.
  | Scan (Fun ScalarBlock) Direction ScalarBlock Var   -- Var is the input array.
                                                       -- ScalarBlock computes the initial value(s).
    
  -- Coming soon: Fold and scan will handle more than one input arrays once we add arrays-of-tuples: 
  --  Fold (Fun ScalarBlock) ScalarBlock [Var] (Maybe Var) -- A possibly segmented fold.
  --  Scan (Fun ScalarBlock) Direction ScalarBlock [Var]
  --  Cond Exp [Var] [Var]

  -- Omitted for now: forward permute and stencils:
  --  Permute (Fun ScalarBlock) Var (Fun ScalarBlock) Var
  --  Error String Exp        -- Signal an error.
  deriving (Read,Show,Eq,Ord,Generic)

data Direction = LeftScan | RightScan
 deriving (Read,Show,Eq,Ord,Generic)           
          
------------------------------------------------------------
-- Accelerate Scalar Expressions and Functions
------------------------------------------------------------

-- | Arbitrary arity functions
data Fun a = Lam [(Var,Type)] a
 deriving (Read,Show,Eq,Ord,Generic)

-- | A scalar code block contains: 
--   * variable decls 
--   * a list of final result variables, 
--   * and a list of statements
data ScalarBlock = ScalarBlock [(Var,Type)] [Var] [Stmt]
 deriving (Read,Show,Eq,Ord,Generic)           
          
data Stmt =   
--    SCond Exp ScalarBlock ScalarBlock
    SCond Exp [Stmt] [Stmt]
  | SSet Var Exp
 deriving (Read,Show,Eq,Ord,Generic)               
          
data Exp = 
    EConst SA.Const           
  | EVr Var                  
  | EPrimApp Type Prim [Exp]
  | ECond Exp Exp Exp        
  | EIndexScalar Var Exp Int  -- Reads a tuple from an array, and does index-from-right into that tuple.
 deriving (Read,Show,Eq,Ord,Generic)


--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | O(N): look up a specific binding in a list of bindings.
--
-- In most cases you will want to create a Data.Map rather than using
-- this function so as to avoid quadratic complexity.
lookupProgBind :: Var -> [LLProgBind a] -> Maybe (LLProgBind a)
lookupProgBind _ [] = Nothing
lookupProgBind v (pb@(LLProgBind vls _ _) : rst)
  | v  `elem` map fst vls = Just pb
  | otherwise = lookupProgBind v rst

expFreeVars :: Exp -> S.Set Var
expFreeVars = fvE

scalarBlockFreeVars :: ScalarBlock -> S.Set Var
scalarBlockFreeVars = fvBlk

stmtFreeVars :: Stmt -> S.Set SA.Var
stmtFreeVars = fvStmt

fvBlk :: ScalarBlock -> S.Set SA.Var
fvBlk (ScalarBlock binds _results stmts) =
  S.difference (S.unions$ L.map fvStmt stmts)
               (S.fromList$ L.map fst binds)

fvStmt :: Stmt -> S.Set SA.Var
fvStmt (SSet _ rhs) = fvE rhs
fvStmt (SCond e1 s1 s2) = S.union (fvE e1)
                           $ S.union (S.unions$ L.map fvStmt s1)
                                     (S.unions$ L.map fvStmt s2)

fvE :: Exp -> S.Set SA.Var
fvE ex =
  case ex of
    EConst _            -> S.empty
    EVr vr              -> S.singleton vr  
    ECond e1 e2 e3      -> S.union (fvE e1)  $ S.union (fvE e2) (fvE e3)
    EIndexScalar v e _  -> S.insert v $ fvE e
    EPrimApp _ _ els    -> fvEs els     
 where
  fvEs = L.foldl (\ acc e -> S.union acc (fvE e)) S.empty 


-- TODO: invariant checker
-- checkValidProg


--------------------------------------------------------------------------------
-- BoilerPlate
--------------------------------------------------------------------------------

instance Out a => Out (LLProg a)
instance Out a => Out (LLProgBind a)
instance Out a => Out (Fun a)
instance Out Direction
instance Out TopLvlForm
instance Out Exp
instance Out ScalarBlock
instance Out Stmt

instance Functor LLProgBind where
  fmap fn (LLProgBind vt dec rhs) = LLProgBind vt (fn dec) rhs

instance Functor LLProg where
  fmap fn prog = prog{ progBinds= fmap (fmap fn) (progBinds prog) }
