{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}       

module Data.Array.Accelerate.SimplePasses.LowerExps
       (liftELets, removeScalarTuple)
       where

-- import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import Data.Array.Accelerate.SimplePasses.IRTypes as S
import qualified Data.Array.Accelerate.SimpleAST  as T
import qualified Data.Array.Accelerate.SimpleAST  as C
import           Data.Map                        as M
import           Data.List                       as L

import Control.Monad.State.Strict (State, runState, get, put)
import Control.Monad (mapM)
import Control.Applicative ((<$>))

type Binding  a = (C.Var, C.Type, a)
type Bindings a = [Binding a]

-- We map each identifier onto both a type and a list of finer-grained (post-detupling) names.
type Env  = M.Map C.Var [C.Var]
type TEnv = M.Map C.Var C.Type

----------------------------------------------------------------------------------------------------
-- First, a let-lifting pass that also lifts out conditional tests.
----------------------------------------------------------------------------------------------------

-- TODO: Use a better approach for coining fresh temporaries.  It
-- would help to form a Set of all existing variables, or to simply
-- keep a Map that freshens ids on the way down.

liftELets :: S.Exp -> S.Exp
liftELets orig = discharge $ loop orig
 where
   addbind bnd = do ls <- get; put (bnd:ls)   
   discharge m = let (x,bnds) = runState m [] in
                 (unpack (reverse bnds) x)
   unpack [] x = x
   unpack (bnd:rst) x = S.ELet bnd (unpack rst x)
   
   loop :: S.Exp -> State (Bindings S.Exp) (S.Exp)
   loop ex = 
     case ex of 

       S.ELet (v,ty,rhs) bod -> 
          do rhs' <- loop rhs -- Important: Collect these bindings first.
             addbind (v,ty,rhs')
             loop bod       
       
       -- Introduce a temporary for the test expression:
       S.ECond e1 e2 e3 -> do e1' <- loop e1
                              addbind (tmp,C.TBool, e1)
                              return $ S.ECond (S.EVr tmp)
                                      -- Don't lift Let out of conditional:
                                      (discharge$ loop e2) 
                                      (discharge$ loop e3)
          where tmp = C.var "TMP_FIXME"

       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       S.EVr    _   -> return ex
       S.EConst _   -> return ex
       S.EShape avr -> return ex
       S.EShapeSize ex          -> S.EShapeSize <$> loop ex
       S.ETuple ls              -> S.ETuple <$> mapM loop ls
       S.EIndex ls              -> S.EIndex <$> mapM loop ls
       S.EPrimApp ty p args     -> S.EPrimApp ty p <$> mapM loop args
       S.ETupProject ind len ex -> S.ETupProject ind len <$> loop ex
       S.EIndexScalar avr ex    -> S.EIndexScalar avr    <$> loop ex

----------------------------------------------------------------------------------------------------
-- After lifting this pass can remove tuples and make shape representations explicit.
----------------------------------------------------------------------------------------------------

-- | This is not a full pass, rather just a function for converting expressions.
--   This is currently [2012.06.27] used by removeArrayTuple.
removeScalarTuple :: TEnv -> S.Exp -> T.Block
removeScalarTuple tenv expr = 
  stmt [] M.empty  M.empty expr
 where 

  -- Here we touch the outer parts of the expression tree,
  -- transforming it into statement blocks.  This depends critically
  -- on Let's having been lifted.
  stmt :: Bindings T.Exp -> Env -> TEnv -> S.Exp -> T.Block
  stmt acc env tenv e = 
     case e of  
       -- Here we need to know that Let's have already been lifted out of the RHS:
       S.ELet (vr,ty,rhs) bod -> stmt acc' env' tenv' bod
                                 where tenv' = M.insert vr ty tenv       
                                       env'  = M.insert vr (error"FINISHMEEE") env 
                                       acc'  = undefined -- (vr,ty, exp env tenv rhs) : acc
       S.ECond (S.EVr vr) e2 e3 -> T.BCond vr (loop e2) (loop e3)
       S.ECond tst        _  _  -> error$ "removeScalarTuple: test expression in conditional was not a plain variable: "++show tst
       oth                      -> T.BBlock (acc++[]) (exp env tenv oth)
    where loop = stmt acc env tenv 

  -- Here we traverse the expression to remove tuples.
  exp :: Env -> TEnv -> S.Exp -> [T.Exp]
  exp env tenv e = 
     case e of  
       S.ELet (vr,ty,rhs) bod -> error$ "removeScalarTuple: Invariants violated.  Should not encounter ELet here (should have been lifted)."
       
       S.EVr vr | Just ls <- M.lookup vr env -> L.map T.EVr ls
       S.EConst (C.Tup ls)  -> L.map T.EConst ls
       S.EConst c           -> [T.EConst c]
       
       -- ASSUMPTION - no primitives accept or return tuples currently:
       S.EPrimApp ty p args     -> [T.EPrimApp ty p (L.map loop1 args)]
       
       -- Conditionals are guaranteed to have varref tests at this point:
       S.ECond (S.EVr vr) e2 e3 -> zipWith (T.ECond vr) (loop e2) (loop e3)

       S.ETuple ls -> concatMap loop ls       
       S.EIndex ls -> concatMap loop ls  -- Same as a tuple
       
       -- Tuple projection simply becomes a matter of statically selecting the named components:
       S.ETupProject ind len ex -> reverse$ take len $ drop ind $ reverse $ 
                                   loop ex
                                   
       S.EIndexScalar (S.Vr _ avr) ex -> [T.EIndexScalar avr (loop ex)]

       -- We know the dimensionality of arrays; further, shapes are just tuples so they are unpacked here:
       S.EShape (S.Vr _ avr) | Just ty <- M.lookup avr tenv -> 
         L.map (`T.EProjFromShape` avr) $ 
         L.take (tupleNumLeaves ty) [0..]
                
       S.EShapeSize ex -> 
         -- To compute the size we simply generate a '+'-expression over all dimensions:
         [L.foldl1 (\ a b -> T.EPrimApp C.TInt (C.NP C.Add) [a,b]) (loop ex)]
         
       S.EVr vr       -> error$"removeScalarTuple: unbound variable "++show vr
       S.EShape avr   -> error$"removeScalarTuple: unbound Array variable."
       S.ECond e1 _ _ -> error$"removeScalarTuple: invariant violated. ECond test not a var: "++show e1
   where 
      loop = exp env tenv
      loop1 e = case loop e of 
                 [x] -> x
                 ls  -> error$"removeScalarTuple: Expecting one value in this context, received: "++show ls

----------------------------------------------------------------------------------------------------
-- Helpers
                        
tupleNumLeaves :: C.Type -> Int
tupleNumLeaves (C.TTuple ls) = L.sum $ L.map tupleNumLeaves ls
tupleNumLeaves _             = 1
