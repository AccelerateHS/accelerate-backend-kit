{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module provides an interpreter for the lower level (CLike) IR .
--   It includes duplicated code from SimpleInterp.hs
--
--   WARNING -- this code is largely duplicated wrt GPUIR.Interpreter

module Data.Array.Accelerate.BackendKit.IRs.CLike.Interpreter
       (
         -- * Evaluating scalar expressions.
         evalScalarBlock,
         evalExp
       )
       where
       
import           Data.Array.Accelerate.BackendKit.IRs.Metadata()
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc             hiding (Exp(..))
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter (evalPrim, Value(..), unConstVal, unArrVal)
import           Data.Array.Accelerate.BackendKit.IRs.CLike
import           Data.Array.Accelerate.BackendKit.SimpleArray               (indexArray)
import qualified Data.Map  as M
import           Control.Monad.State.Strict

--------------------------------------------------------------------------------
-- Values and Environments:

-- | Environments. Because LLIR includes side effects, the environement is mutable.
type Env = M.Map Var Value

-- | Computations with an environment.
type EnvM = State Env

-- | A helper routine just to get nicer errors:
envLookup :: (Ord k, Show k) => M.Map k a -> k -> a
envLookup env vr = 
  case M.lookup vr env of 
    Just x -> x 
    Nothing -> error$ "LLIRInterp.hs/envLookup: no binding for variable "++show vr

evalScalarBlock :: Env -> ScalarBlock -> [Const]
evalScalarBlock env0 (ScalarBlock _decls results stmts) =
  -- Retrieve the results from the final environment.
  map (unConstVal . (final M.!)) results
  where
    -- We use an untyped evaluation strategy and ignore the decls:
    final = execState (mapM_ evalStmt stmts) env0

-- | Statements are evaluated only for effect:
evalStmt :: Stmt -> EnvM ()
evalStmt (SCond a bs cs) = do
  env <- get
  let B bool = evalExp env a
  if bool
    then mapM_ evalStmt bs
    else mapM_ evalStmt cs
evalStmt (SSet v e) = do
  env <- get
  put (M.insert v (ConstVal$ evalExp env e) env)
evalStmt oth = error "FINISH ME"

-- | Evaluate a scalar expression to a value, using Const as the value representation.
--   Note that this only allows scalar results.
evalExp :: Env -> Exp -> Const
evalExp env expr = 
  case expr of 
    EVr  v             -> unConstVal$ envLookup env v
    EConst c           -> c
    ECond e1 e2 e3     -> let B b = evalExp env e1 in
                          if b then evalExp env e2
                               else evalExp env e3
    EPrimApp ty p es   -> evalPrim ty p (map (evalExp env) es)
    -- This only works for one-dimensional indices:
    EIndexScalar vr ex _n -> indexArray (unArrVal$ envLookup env vr)  
                             [fromIntegral $ constToInteger $ evalExp env ex]

{-
--------------------------------------------------------------------------------

-- | Create a list of Const/int indices corresponding to the index space
--   of an Accelerate array, layed out in the appropriate order for
--   Accelerate.  
--                                  
-- Note that indices in this interpreter are in REVERSE ORDER from
-- Accelerate source code.  The fastest changing dimension is the LEFTMOST.
indexSpace :: [Int] -> [Const]
indexSpace inds = map (tuple . reverse) $ 
                  loop (reverse inds)
  where 
    loop :: [Int] -> [[Const]]
    loop []  = []
    loop [n] = map (\i -> [I i]) [0..n-1]
    loop (hd:tl) = 
      let rest = loop tl in
      concatMap (\ i -> map (I i:) rest)
                [0..hd-1]
  -- map I [0..n-1]
           

-- Unary tuples do not exist in the language:
tuple :: [Const] -> Const
tuple [x] = x
tuple ls  = Tup ls

-- This currently handles nested Tups, but we generally insure those won't occur:
untuple :: Const -> [Const]
untuple (Tup ls) = concatMap untuple ls
untuple oth = [oth]

tupleVal :: [Value] -> Value
tupleVal [x] = x
tupleVal ls  = TupVal ls

-- This goes inside both types of tuples (Val and Const).
untupleVal :: Value -> [Value]
untupleVal (TupVal ls)  = concatMap untupleVal ls
untupleVal (ConstVal c) = map ConstVal $ untuple c
untupleVal (ArrVal a)   = [ArrVal a]

-}
--------------------------------------------------------------------------------
