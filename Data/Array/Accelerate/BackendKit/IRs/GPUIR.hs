{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}


module Data.Array.Accelerate.BackendKit.IRs.GPUIR
       (
         -- * GPUIR: intermediate representation isomorphic to GPU code
         GPUProg(..), GPUProgBind(..), TopLvlForm(..), ScalarBlock(..), Stmt(..), Exp(..),
         Fun(..), MemLocation(..), Direction(..), Segmentation(..), EvtId,

         -- * Helper functions for the GPUIR
         lookupProgBind, expFreeVars, stmtFreeVars, scalarBlockFreeVars
       )
       where

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SA
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Var,Type,AccArray)
import qualified Data.Set  as S
import           Data.List as L
import           Text.PrettyPrint.GenericPretty (Out, Generic)
import           Data.Array.Accelerate.BackendKit.IRs.CLike (Direction(..))

----------------------------------------------------------------------------------------------------
-- Low Level Intermediate Representation
----------------------------------------------------------------------------------------------------

-- | The low-level AST.
data GPUProg decor = GPUProg { 
  progBinds     :: [GPUProgBind decor],
  progResults   :: [Var],
  uniqueCounter :: Int,
  progType      :: Type, -- Final, pre-flattened type, can be an array-tuple.
  -- A table mapping the name of a top-level array to the last event
  -- that we need to wait on to fill it:
  lastwriteTable :: [(Var,EvtId)]
  --  writerMap  :: M.Map Var EvtId -- No Generic yet
} deriving (Read,Show,Eq,Generic, Ord)

-- | A progbind may bind multiple arrays simultaneously.  The unzipped
-- nature of arrays is exposed directly in the AST at this point.
-- 
-- For example, a Generate parameterized by a ScalarBlock that returns
-- three values will in turn produce three arrays.  All three arrays
-- must be the same shape.
data GPUProgBind d = GPUProgBind {
      evtid   :: EvtId,
      evtdeps :: [EvtId], 
      outarrs :: [(Var,MemLocation,Type)],
      decor   :: d,
      op      :: TopLvlForm
    }
    deriving (Read,Show,Eq,Generic, Ord)

type EvtId = Var

------------------------------------------------------------
-- Accelerate Array-level Expressions
------------------------------------------------------------

-- A top level operation, including array and scalar expressions.
data TopLvlForm =   
    ScalarCode ScalarBlock -- A block of Scalar code binding one or more variables.
  | Cond Exp Var Var
  | Use       AccArray

  -- Create a new array of the specified # elements:
  | NewArray Exp 

  -- A GPU kernel.  There is no implicit output array (like with
  -- Generate).  Scalar and array arguments to the kernel must be
  -- explicit:
  | Kernel  { kerniters :: [(Var,Exp)],     -- Each variable ranges from 0 to Exp-1
              kernbod   :: Fun ScalarBlock, -- The arguments here are kernargs NOT the indices
              kernargs  :: [Exp] }

  -- These rest of the operators are ONLY, here to support initial
  -- translation and possible additional optimization.  They must be
  -- eliminated before a GPU backend is expected to run.
  ------------------------------------------------------------
  -- Generate carries the individual dimension components [Exp]
  | Generate  [Exp] (Fun ScalarBlock)
  | Fold (Fun ScalarBlock) [Exp] Var Segmentation -- ^ A possibly segmented fold.
  | Scan (Fun ScalarBlock) Direction [Exp] Var    -- ^ [Exp] provides the initial accumulator value(s)
    
  deriving (Read,Show,Eq,Ord,Generic)

data Segmentation = VariableStride Var -- The name of an array containing the strides.
                  | ConstantStride Exp -- A constant segmentation.
  deriving (Read,Show,Eq,Ord,Generic)

------------------------------------------------------------
-- Accelerate Scalar Expressions and Functions
------------------------------------------------------------

-- | Arbitrary arity functions
data Fun a = Lam [(Var,MemLocation,Type)] a
 deriving (Read,Show,Eq,Ord,Generic)

-- | A scalar code block contains: 
--   * variable decls 
--   * a list of final result variables, 
--   * and a list of statements
data ScalarBlock = ScalarBlock [(Var,MemLocation,Type)] [Var] [Stmt]
 deriving (Read,Show,Eq,Ord,Generic)           
          
data Stmt =   
    SCond Exp [Stmt] [Stmt]
  | SSet    Var Exp             -- v = exp
  | SArrSet Var Exp Exp         -- arr[exp] = exp
  | SFor { forvar :: Var,
           forinit :: Exp,
           fortest :: Exp,
           forincr :: Exp,
           forbody :: [Stmt]
           }                    -- for (init,test,incr) { body }
  | SNoOp                       -- no operation
  | SSynchronizeThreads

    -- Comments to be emitted to generated code:
  | SComment String
 deriving (Read,Show,Eq,Ord,Generic)

data MemLocation = Default | Global | Local | Private | Constant 
 deriving (Read,Show,Eq,Ord,Generic)

data Exp = 
    EConst SA.Const           
  | EVr Var
  | EGetLocalID  Int            -- The Int specifies dimension: 0,1,2
  | EGetGlobalID Int 
  | EPrimApp Type SA.Prim [Exp]
  | ECond Exp Exp Exp        
  | EIndexScalar Var Exp        -- Reads a tuple from an array, and does index-from-right into that tuple.
  | EUnInitArray Type Int       -- This is ONLY here as a special OpenCL convention.  "Local" memory
                                -- arrays are passed into the kernel as NULL ptrs WITH sizes (here in #elements).
 deriving (Read,Show,Eq,Ord,Generic)

-- data WhichDim = DimX | DimY | DimZ
--  deriving (Read,Show,Eq,Ord,Generic)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | O(N): look up a specific binding in a list of bindings.
--
-- In most cases you will want to create a Data.Map rather than using
-- this function so as to avoid quadratic complexity.
lookupProgBind :: Var -> [GPUProgBind a] -> Maybe (GPUProgBind a)
lookupProgBind _ [] = Nothing
lookupProgBind v (pb@(GPUProgBind{outarrs}) : rst)
  | v  `elem` map fst3 outarrs = Just pb
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
               (S.fromList$ L.map fst3 binds)

doStmt :: Stmt -> S.Set SA.Var
doStmt st =
  case st of
    SNoOp               -> S.empty
    SSynchronizeThreads -> S.empty
    SSet _ rhs     -> doE rhs
    SCond e1 s1 s2 -> S.union (doE e1) $ 
                      S.union (doStmts s1) (doStmts s2)
    SArrSet _ ind rhs     -> S.union (doE ind) (doE rhs) 
    SFor v accinit test incr bod -> S.delete v $
                                    S.unions [doE accinit, doE test, doE incr,
                                              doStmts bod]

doStmts :: [Stmt] -> S.Set SA.Var
doStmts = S.unions .  L.map doStmt

doE :: Exp -> S.Set SA.Var
doE ex =
  case ex of
    EConst _            -> S.empty
    EGetGlobalID _      -> S.empty
    EGetLocalID  _      -> S.empty    
    EVr vr              -> S.singleton vr  
    ECond e1 e2 e3      -> S.union (doE e1)  $ S.union (doE e2) (doE e3)
    EIndexScalar v e    -> S.insert v $ doE e
    EPrimApp _ _ els    -> doEs els
 where
  doEs = L.foldl (\ acc e -> S.union acc (doE e)) S.empty 


fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a

-- TODO: invariant checker
-- checkValidProg

--------------------------------------------------------------------------------
-- BoilerPlate
--------------------------------------------------------------------------------

instance Out a => Out (GPUProg a)
instance Out a => Out (GPUProgBind a)
instance Out a => Out (Fun a)
instance Out TopLvlForm
instance Out ScalarBlock
instance Out Stmt
instance Out Exp
instance Out MemLocation
instance Out Segmentation


instance Functor GPUProgBind where
  fmap fn (pb@GPUProgBind{decor}) = pb{decor= (fn decor)}

instance Functor GPUProg where
  fmap fn prog = prog{ progBinds= fmap (fmap fn) (progBinds prog) }
