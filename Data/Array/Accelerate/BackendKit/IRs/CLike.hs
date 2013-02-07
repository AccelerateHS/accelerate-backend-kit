
{-# LANGUAGE DeriveGeneric #-}

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
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Var,Type,Prim,AccArray)
import           Text.PrettyPrint.GenericPretty (Out, Generic)
import qualified Data.Set as S
import           Data.List          as L

----------------------------------------------------------------------------------------------------
-- Low Level Intermediate Representation
----------------------------------------------------------------------------------------------------

-- | The Low-Level (C-like) AST.
data LLProg decor = LLProg { 
  progBinds   :: [LLProgBind decor],
  progResults :: [Var],
  uniqueCounter :: Int,
  progType    :: Type -- Final, pre-flattened type, can be an array-tuple.

  -- | Describes the type and shape of all top level binds.  The list has length
  -- equal to the number of dimensions.
--  sizeEnv :: M.Map Var (Type, [TrivialExp])
  
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
expFreeVars = doE

scalarBlockFreeVars :: ScalarBlock -> S.Set Var
scalarBlockFreeVars = doBlk

stmtFreeVars :: Stmt -> S.Set SA.Var
stmtFreeVars = doStmt

doBlk :: ScalarBlock -> S.Set SA.Var
doBlk (ScalarBlock binds _results stmts) =
  S.difference (S.unions$ L.map doStmt stmts)
               (S.fromList$ L.map fst binds)

doStmt :: Stmt -> S.Set SA.Var
doStmt (SSet _ rhs) = doE rhs
doStmt (SCond e1 s1 s2) = S.union (doE e1)
                           $ S.union (S.unions$ L.map doStmt s1)
                                     (S.unions$ L.map doStmt s2)

doE :: Exp -> S.Set SA.Var
doE ex =
  case ex of
    EConst _            -> S.empty
    EVr vr              -> S.singleton vr  
    ECond e1 e2 e3      -> S.union (doE e1)  $ S.union (doE e2) (doE e3)
    EIndexScalar v e _  -> S.insert v $ doE e
    EPrimApp _ _ els    -> doEs els     
 where
  doEs = L.foldl (\ acc e -> S.union acc (doE e)) S.empty 


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
