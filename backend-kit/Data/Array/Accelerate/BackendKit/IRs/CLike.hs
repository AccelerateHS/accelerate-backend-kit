
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

-- | A lower-level intermediate representation that has certain notable differences
-- from Accelerate's front-end representation.  Everything is one dimensional, and
-- there are no tuples at the array or scalar levels.  Accordingly, array operations
-- potentially have more than one output binding, and the lambdas that parameterize
-- them may have more (untupled) arguments than before.  The set of array operators
-- is also greatly reduced.
--
-- Scalar computations explicitly separate statements from expressions, making code
-- generation to C-like languages easy.  ScalarBlock's effectively have multiple
-- return values.
--
-- The language is still purely functional.

module Data.Array.Accelerate.BackendKit.IRs.CLike
       (
         -- * LLIR: modified, lower-level versions of the AST in
         -- "Data.Array.Accelerate.SimpleAST".  Full documentation not
         -- duplicated here.
         LLProg(..), LLProgBind(..), TopLvlForm(..), ScalarBlock(..), Stmt(..), Exp(..),
         Direction(..), Fun(..), ReduceVariant(..), Stride(..), MGenerator(..), Generator(..),

         -- * Helper functions for the LLIR 
         lookupProgBind, expFreeVars, stmtFreeVars, scalarBlockFreeVars,
         simpleBlockToExp, expsToBlock
       )
       where

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SA
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (AVar,Var,Type,Prim,AccArray,TrivialExp)
import           Data.Array.Accelerate.BackendKit.IRs.Metadata (Stride(..))
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (GensymM, genUnique)

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
  -- Due to tuple unzipping, the shape will now be a list of shape components:
  progResults :: [(AVar,[Var])],
  uniqueCounter :: Int,
  progType    :: Type, -- Final, pre-flattened type, can be an array-tuple.

  -- | Describes the ELEMENT type and shape of all top level ARRAY binds (scalar binds not
  -- included).  All arrays are one-dimensional at this point, so size is a scalar.
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
  | Use          AccArray
  | Use'     Var AccArray -- Part of my Use* hack. I'm still upset that I can't use * at the end of a name.

  -- | Generate an array, storing it in memory
  | GenManifest (Generator (Fun ScalarBlock))

  -- | GenReduce both produces (or fetches) elements and combines them.  It is
  -- parameterized first by a reduce function and second by a generate function.  The
  -- generate function takes an index position via one or more arguments and produces
  -- intermediate reduction value(s).  The reducer function takes two SETS of
  -- reduction values (the left and right halves of its argument list) and returns
  -- one set.  The `GenReduce` produces the same number of output arrays as the
  -- reduction function produces values.
  | GenReduce {
      reducer    :: Fun ScalarBlock,
      generator  :: MGenerator (Fun ScalarBlock), 
      variant    :: ReduceVariant Fun ScalarBlock,
      stride     :: Stride Exp }
  -- Omitted for now: STENCILS:
  deriving (Read,Show,Eq,Ord,Generic)

-- | A Generate construct: a functional description of an array.
data Generator fun = Gen TrivialExp fun
  deriving (Read,Show,Eq,Ord,Generic)

-- | A reference to /either/ a manifest (existing in memory) array, or a functional
-- description of an array.
data MGenerator fn = Manifest [Var] 
                   | NonManifest (Generator fn)
  deriving (Read,Show,Eq,Ord,Generic)
           
-- | All the kinds of array ops that involve /reduction/.  All fold/scan variants
-- carry an initial element (`ScalarBlock`). Segmented variants include also include
-- an array containing the segment descriptor.
data ReduceVariant fn sb =
    Fold              sb
  | FoldSeg           sb (MGenerator (fn sb))
  | Scan    Direction sb
-- BJS: How tell apart Scan and Scan1 and Scan' ?
  | Scan1   Direction
  | Fold1 -- Fold1 has no direction or sb
    -- | Forward permute also takes a default array and an
    -- index-permuting function:
  | Permute { permfun:: fn sb, defaults::MGenerator (fn sb) }
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
          
-- Moving While to be a statement, beacause we believe it to be the right thing  
-- to do.

--    SCond Exp ScalarBlock ScalarBlock
data Stmt = SCond Exp [Stmt] [Stmt]
          --       condvar  cond                 body       init  
          | SWhile Var (Fun ScalarBlock)  (Fun ScalarBlock) ScalarBlock --Exp
          | SSet Var Exp
 deriving (Read,Show,Eq,Ord,Generic)               
          
data Exp = 
    EConst SA.Const           
  | EVr Var                  
  | EPrimApp Type Prim [Exp]
  | ECond Exp Exp Exp    
--  | EWhile (Fun Exp) (Fun Exp) Exp     
  | EIndexScalar Var Exp Int  -- Reads a tuple from an array, and does index-from-right into that tuple.
    -- TODO: get rid of the numeric argument when tupling is fully eliminated.
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

--ScalarBlock [(Var,Type)] [Var] [Stmt]
fvStmt (SWhile v (Lam binds1 (ScalarBlock locals1 v1 stms1) )
        (Lam binds2 (ScalarBlock locals2 v2 stms2))
        (ScalarBlock locals3 v3 stms3)) = 
    let fv_sb1 = S.unions $ L.map fvStmt stms1
        fv_sb2 = S.unions $ L.map fvStmt stms2
        fv_sb3 = S.unions $ L.map fvStmt stms3
        tmp =  fv_sb1 `S.union` fv_sb2 `S.union` fv_sb3
        dels = S.fromList $ map fst (binds1 L.++ binds2 L.++ locals1 L.++ locals2 L.++ locals3)
    in  S.difference tmp dels 


fvE :: Exp -> S.Set SA.Var
fvE ex =
  case ex of
    EConst _            -> S.empty
    EVr vr              -> S.singleton vr  
    ECond e1 e2 e3      -> S.union (fvE e1)  $ S.union (fvE e2) (fvE e3)
    -- EWhile (Lam [(v1,t1)] bod1) 
    --        (Lam [(v2,t2)] bod2) e -> 
    --    let s1 = S.delete v1 $fvE bod1 
    --        s2 = S.delete v1 $fvE bod2 
           
    --    in s1 `S.union` s2 `S.union` (fvE e) 
    EIndexScalar v e _  -> S.insert v $ fvE e
    EPrimApp _ _ els    -> fvEs els     
 where
  fvEs = L.foldl (\ acc e -> S.union acc (fvE e)) S.empty 

-- | Simple blocks are really just expressions in disguise.
simpleBlockToExp :: ScalarBlock -> Maybe Exp
simpleBlockToExp sb@(ScalarBlock [(v1,t)] [v2] [SSet v3 e]) =
  if v1 == v2 && v2 == v3
  then Just e
  else error$"simpleBlockToExp: ScalarBlock looks corrupt: "++show sb
simpleBlockToExp _ = Nothing

-- | Take any number of Exps (with types) and package them as a `ScalarBlock`.
expsToBlock :: [(Exp,Type)] -> GensymM ScalarBlock
expsToBlock binds = do
  -- u <- genUnique
  -- return $ ScalarBlock [(u,ty)] [u] [SSet u ex]
  let (exs,tys) = unzip binds
  us <- sequence$ replicate (length binds) genUnique
  return $ ScalarBlock (zip us tys) us (zipWith SSet us exs)


-- TODO: invariant checker
-- checkValidProg

--------------------------------------------------------------------------------
-- BoilerPlate
--------------------------------------------------------------------------------

instance Out a => Out (LLProg a)
instance Out a => Out (LLProgBind a)
instance Out a => Out (Fun a)
instance Out Direction
instance (Out a, Out (fn a)) => Out (ReduceVariant fn a)
instance Out a => Out (Generator a)
instance Out a => Out (MGenerator a)
instance Out TopLvlForm
instance Out Exp
instance Out ScalarBlock
instance Out Stmt

instance Functor LLProgBind where
  fmap fn (LLProgBind vt dec rhs) = LLProgBind vt (fn dec) rhs

instance Functor LLProg where
  fmap fn prog = prog{ progBinds= fmap (fmap fn) (progBinds prog) }
