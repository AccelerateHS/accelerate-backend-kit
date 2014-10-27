{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | The lowest-level AST containing a very different ProgBind type.

module Data.Array.Accelerate.BackendKit.IRs.GPUIR
       (
         -- * GPUIR: intermediate representation isomorphic to GPU code
         GPUProg(..), GPUProgBind(..), TopLvlForm(..), ScalarBlock(..), Stmt(..), Exp(..),
         MemLocation(..), EvtId,

         -- * Reexport for completeness:
         Fun(..), Direction(..), ReduceVariant(..), MGenerator(..), Generator(..), Stride(..),

         -- * Helper functions for the GPUIR
         lookupProgBind, expFreeVars, stmtFreeVars, scalarBlockFreeVars, trivToExp,
         simpleBlockToExp, expsToBlock,
         
         -- * Helpers for constructing bits of AST syntax while incorporating small optimizations.
         addI, mulI, quotI, remI, maxI, minI, 
       )
       where

import qualified Data.Set  as S
import qualified Data.Map  as M
import           Data.List as L
import           Prelude as P
import           Text.PrettyPrint.GenericPretty (Out, Generic)

import           Data.Array.Accelerate.BackendKit.Utils.Helpers (GensymM, genUnique)
import           Data.Array.Accelerate.BackendKit.IRs.Metadata (Stride(..))
import           Data.Array.Accelerate.BackendKit.IRs.CLike (Direction(..), ReduceVariant(..),
                                                             MGenerator(..), Generator(..))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SA
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                   (AVar,Var,Type,AccArray, Prim(..), Const(..), Type(..), TrivialExp)


----------------------------------------------------------------------------------------------------
-- Low Level Intermediate Representation
----------------------------------------------------------------------------------------------------

-- | The lowest-level AST containing a very different ProgBind type.
data GPUProg decor = GPUProg { 
  progBinds     :: [GPUProgBind decor],
  progResults   :: [(AVar,[Var])],
  uniqueCounter :: Int,
  progType      :: Type, -- ^ Final, pre-flattened type, can be an array-tuple.
  
  sizeEnv :: M.Map Var (Type, TrivialExp), -- ^ Same as CLike IR (LLProg)
  
  -- | A table mapping the name of a top-level array to the last event
  --   that we need to wait on to fill it:
  lastwriteTable :: [(Var,EvtId)]
  --  writerMap  :: M.Map Var EvtId -- No Generic yet
} deriving (Read,Show,Eq,Generic, Ord)

-- | A progbind may bind multiple arrays simultaneously.  The unzipped
-- nature of arrays is exposed directly in the AST at this point.
-- 
-- A top level binding also at this point corresponds to a GPU
-- scheduler *event* with explicit dependencies on other events.
-- However, for some top level bindings that don't execute on the GPU
-- (e.g. ScalarCode) these are ignored.
--
-- All arrays written by a TopLvlForm (implicitly or explicitly) are
-- counted in the `outarrs` list.  For example, a Generate
-- parameterized by a ScalarBlock that returns three values will in
-- turn produce three arrays.  All three arrays must be the same
-- shape.  On the other hand, a `Kernel` may write to as many arrays of
-- whatever shapes it likes.
-- 
-- `outarrs` is actually kind of multi-purpose, because scalar
-- bindings also produce output bindings, which are not arrays.
data GPUProgBind d = GPUProgBind {
      evtid   :: EvtId,                    -- ^ EventID for this operator's execution.      
      evtdeps :: [EvtId],                  -- ^ Dependencies for this operator.      
      outarrs :: [(Var,MemLocation,Type)], -- ^ Outputs of this operator.
      decor   :: d,                        -- ^ Parameterizable decoration
      op      :: TopLvlForm                -- ^ The operator itself.
    }
    deriving (Read,Show,Eq,Generic, Ord)

type EvtId = Var

------------------------------------------------------------
-- Accelerate Array-level Expressions
------------------------------------------------------------

-- | A top level operation, including array and scalar expressions.
data TopLvlForm =   
    ScalarCode ScalarBlock -- A block of Scalar code binding one or more variables.
  | Cond Exp Var Var
  | Use       AccArray

  -- | Create a new array of the specified # elements:
  | NewArray Exp 

  -- | A GPU kernel.  There is no implicit output array (like with
  --   Generate).  Scalar and array arguments to the kernel must be
  --   explicit:
  | Kernel  { kerniters :: [(Var,Exp)],     -- N dimensions.  Each variable ranges from 0 to Exp-1 independently.
              kernbod   :: Fun ScalarBlock, -- /Closed/ function.  The arguments here are kernargs NOT the indices.
              kernargs  :: [Exp] }

  -- These rest of the operators are ONLY here to support initial
  -- translation and possible additional optimization.  They MUST be
  -- converted to raw `Kernel`s before a GPU backend is expected to run.
  ----------------------------------------------------------------------
  | GenManifest (Generator (Fun ScalarBlock))

  -- | The same as in CLike.hs, see docs there:
  | GenReduce {
      reducer    :: Fun ScalarBlock,
      generator  :: MGenerator (Fun ScalarBlock), 
      variant    :: ReduceVariant Fun ScalarBlock,
      stride     :: Stride Exp }
        
  deriving (Read,Show,Eq,Ord,Generic)

data Segmentation = VariableStride Var -- The name of an array containing the strides.
                  | ConstantStride Exp -- A constant segmentation, which might just be the whole array.
  deriving (Read,Show,Eq,Ord,Generic)


------------------------------------------------------------
-- Accelerate Scalar Expressions and Functions
------------------------------------------------------------

-- | Arbitrary arity functions.  Differs from CLike.hs in that memory location is
-- also tracked.
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
  | SWhile Var (Fun ScalarBlock) (Fun ScalarBlock) ScalarBlock
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
-- This guy now has statement status 
--   | EWhile (Fun Exp) (Fun Exp) Exp      
  | EIndexScalar Var Exp        -- Reads a tuple from an array, and does index-from-right into that tuple.
  | EUnInitArray Type Int       -- This is ONLY here as a special OpenCL convention.  "Local" memory
                                -- arrays are passed into the kernel as NULL ptrs WITH sizes (here in #elements).
 deriving (Read,Show,Eq,Ord,Generic)

-- data WhichDim = DimX | DimY | DimZ
--  deriving (Read,Show,Eq,Ord,Generic)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | A simple conversion to the GPUIR version of `Exp`.
trivToExp :: SA.TrivialExp -> Exp
trivToExp (SA.TrivConst n)  = EConst (I n)
trivToExp (SA.TrivVarref v) = EVr v

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
    SArrSet _ ind rhs -> doE ind `S.union` doE rhs
    SFor v accinit test incr bod -> S.delete v $
                                    S.unions [doE accinit, doE test, doE incr,
                                              doStmts bod]

doStmts :: [Stmt] -> S.Set SA.Var
doStmts = S.unions .  L.map doStmt

-- COLLECT FREE VARS 
doE :: Exp -> S.Set SA.Var
doE ex =
  case ex of
    EConst _            -> S.empty
    EGetGlobalID _      -> S.empty
    EGetLocalID  _      -> S.empty    
    EVr vr              -> S.singleton vr  
    ECond e1 e2 e3      -> S.union (doE e1)  $ S.union (doE e2) (doE e3)
--    EWhile (Lam [(v1,_,t1)] bod1) (Lam [(v2,_,t2)] bod2) e ->
--        let s1 = S.delete v1 $doE bod1 
--            s2 = S.delete v1 $doE bod2    
--        in s1 `S.union` s2 `S.union` (doE e) 
       
    EIndexScalar v e    -> S.insert v $ doE e
    EPrimApp _ _ els    -> doEs els
 where
  doEs = L.foldl (\ acc e -> S.union acc (doE e)) S.empty 


fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a

-- TODO: invariant checker
-- checkValidProg

--------------------------------------------------------------------------------
-- <DUPLICATED CODE FROM CLike.hs>

-- | Simple blocks are really just expressions in disguise.
simpleBlockToExp :: ScalarBlock -> Maybe Exp
simpleBlockToExp sb@(ScalarBlock [(v1,Default,t)] [v2] [SSet v3 e]) =
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
  return $ ScalarBlock (zip3 us (repeat Default) tys) us
                       (zipWith SSet us exs)

-- </DUPLICATED CODE FROM CLike.hs>
--------------------------------------------------------------------------------

-- Convenient integer operations
addI :: Exp -> Exp -> Exp
addI (EConst (I 0)) n = n
addI n (EConst (I 0)) = n
addI (EConst (I n)) (EConst (I m)) = EConst$ I$ n + m
addI n m              = EPrimApp TInt (NP SA.Add) [n,m]

mulI :: Exp -> Exp -> Exp
mulI (EConst (I 0)) _ = EConst (I 0)
mulI _ (EConst (I 0)) = EConst (I 0)
mulI (EConst (I 1)) n = n
mulI n (EConst (I 1)) = n
mulI (EConst (I n)) (EConst (I m)) = EConst$ I$ n * m
mulI n m              = EPrimApp TInt (NP SA.Mul) [n,m]

quotI :: Exp -> Exp -> Exp
quotI n (EConst (I 1)) = n
quotI (EConst (I n)) (EConst (I m)) = EConst$ I$ P.quot n m
quotI n m              = EPrimApp TInt (IP SA.Quot) [n,m]

remI :: Exp -> Exp -> Exp
remI _ (EConst (I 1)) = EConst (I 0)
remI (EConst (I n)) (EConst (I m)) = EConst$ I$ P.rem n m
remI n m              = EPrimApp TInt (IP SA.Rem) [n,m]

maxI :: Exp -> Exp -> Exp
maxI (EConst (I n)) (EConst (I m)) = EConst$ I$ P.max n m
maxI n m                           = EPrimApp TInt (SP SA.Max) [n,m]

minI :: Exp -> Exp -> Exp
minI (EConst (I n)) (EConst (I m)) = EConst$ I$ P.min n m
minI n m                           = EPrimApp TInt (SP SA.Min) [n,m]

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
