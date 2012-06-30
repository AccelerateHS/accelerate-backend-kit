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
import Control.Monad (mapM, (=<<))
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
   
   isLet (S.ELet _ _) = True
   isLet _            = False

   -- TODO: Do real temporary generation:
   mkTmp = return$ C.var "TMP_FIXME"

   liftOut ty rhs = do
     tmp <- mkTmp 
     addbind (tmp,ty,rhs)
     return (S.EVr tmp)

   -- The rules are different for what is allowed in a Let-RHS:
   loopRHS :: S.Exp -> State (Bindings S.Exp) (S.Exp)
   loopRHS ex = 
     case ex of
       -- Introduce a temporary for the test expression:
       S.ECond e1 e2 e3 -> do 
         let e2' = (discharge$ loop e2) 
             e3' = (discharge$ loop e3)
         -- Lift the test expression out only if necessary:           
         e1' <- if S.isTrivial e1 
                then return e1
                else liftOut C.TBool =<< loop e1
         return $ S.ECond e1' e2' e3'
       
       oth -> loop ex
     
   loop :: S.Exp -> State (Bindings S.Exp) (S.Exp)
   loop ex = 
     case ex of 

       S.ELet (v,ty,rhs) bod -> 
          do rhs' <- loopRHS rhs -- Important: Collect these bindings first.
             addbind (v,ty,rhs')
             loop bod       
       
       S.ECond _ _ _ -> do 
         rhs@(S.ECond _ e2 e3) <- loopRHS ex
         -- If either of the branches is a let this conditional must itself occur in a Let-RHS.
         if isLet e2 || isLet e3 
           then liftOut (error"FIXME-SETTHISTYPE") rhs
           else return rhs
         
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       S.EVr    _               -> return ex
       S.EConst _               -> return ex
       S.EShape avr             -> return ex
       S.EShapeSize ex          -> S.EShapeSize <$> loop ex
       S.ETuple ls              -> S.ETuple <$> mapM loop ls
       S.EIndex ls              -> S.EIndex <$> mapM loop ls
       S.EPrimApp ty p args     -> S.EPrimApp ty p <$> mapM loop args
       S.ETupProject ind len ex -> S.ETupProject ind len <$> loop ex
       S.EIndexScalar avr ex    -> S.EIndexScalar avr    <$> loop ex
       
       S.EIndexConsDynamic _ _ -> error$"liftELets: no dynamic indexing at this point"
       S.EIndexHeadDynamic _   -> error$"liftELets: no dynamic indexing at this point"
       S.EIndexTailDynamic _   -> error$"liftELets: no dynamic indexing at this point"


-- Count the number of total variables in an expression.  This is used
-- as the basis for coining new unique identifiers.  IDEALLY ASTs
-- would keep this information around so that it doesn't need to be
-- recomputed.
countVars ex =
  case ex of
    S.ELet (_,_,rhs) bod     -> 1 + countVars rhs + countVars bod
    S.EVr    _               -> 0
    S.EConst _               -> 0
    S.EShape avr             -> 0
    S.EShapeSize ex          -> countVars ex
    S.ETuple ls              -> sum $ L.map countVars ls
    S.EIndex ls              -> sum $ L.map countVars ls
    S.EPrimApp ty p args     -> sum $ L.map countVars args
    S.ETupProject ind len ex -> countVars ex
    S.EIndexScalar avr ex    -> countVars ex
    S.EIndexConsDynamic e1 e2 -> countVars e1 + countVars e2
    S.EIndexHeadDynamic e     -> countVars e
    S.EIndexTailDynamic e     -> countVars e
    S.ECond a b c             -> countVars a + countVars b + countVars c

----------------------------------------------------------------------------------------------------
-- After lifting this pass can remove tuples and make shape representations explicit.
----------------------------------------------------------------------------------------------------

-- | This is not a full pass, rather just a function for converting expressions.
--   This is currently [2012.06.27] used by removeArrayTuple.
removeScalarTuple :: TEnv -> S.Exp -> T.Block
removeScalarTuple tenv expr = 
  stmt [] M.empty  M.empty expr
 where 
  -- We do NOT aim for global uniqueness here.  This will only give us
  -- uniqueness the expression expr.
  -- numVars = countVars expr
  tmproot = "tmpRST"
   
  -- Here we touch the outer parts of the expression tree,
  -- transforming it into statement blocks.  This depends critically
  -- on Let's having been lifted.
  stmt :: Bindings T.Exp -> Env -> TEnv -> S.Exp -> T.Block
  stmt acc env tenv e = 
     case e of  
       -- Here's where we need to split up a binding into a number of new temporaries:
       S.ELet (vr,ty, S.ECond a b c) bod ->          
              -- Uh oh, we need temporaries here:
             T.BMultiLet (tmps, error "split tuptype here", T.BCond vr conseq altern) $ 
             stmt acc' env' tenv' bod
         where tmps = take (tupleNumLeaves ty) (repeat vr) -- FIXME FIXME
               S.EVr vr = a
               tenv' = M.insert vr ty tenv       
               env'  = M.insert vr (error"FINISHMEEE") env 
               acc'  = error "finish acc1" -- (vr,ty, exp env tenv rhs) : acc
               conseq = stmt undefined env tenv b 
               altern = stmt undefined env tenv c 
       
       -- Here we need to know that Let's have already been lifted out of the RHS to call exp:
       S.ELet (vr,ty,rhs) bod -> stmt acc' env' tenv' bod
         where tenv' = M.insert vr ty tenv       
               env'  = M.insert vr (error"FINISHMEEE2") env 
               acc'  = error "finish acc2" -- (vr,ty, exp env tenv rhs) : acc
--       S.ECond (S.EVr vr) e2 e3 -> T.BCond vr (loop e2) (loop e3)
       S.ECond tst        _  _  -> error$ "removeScalarTuple: test expression in conditional was not a plain variable: "++show tst
       oth                      -> T.BResults (exp env tenv oth)
    where loop = stmt acc env tenv 

  -- Here we traverse the expression to remove tuples.
  exp :: Env -> TEnv -> S.Exp -> [T.Exp]
  exp env tenv e = 
     case e of  
       
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
       S.EIndexScalar ae _ -> error$"removeScalarTuple: invariant broken: non-varref arg to EIndexScalar"
       S.EIndexConsDynamic _ _ -> error$"removeScalarTuple: no dynamic indexing at this point"
       S.EIndexHeadDynamic _   -> error$"removeScalarTuple: no dynamic indexing at this point"
       S.EIndexTailDynamic _   -> error$"removeScalarTuple: no dynamic indexing at this point"         
       S.ELet (vr,ty,rhs) bod -> 
         error$ "removeScalarTuple: Invariants violated.  Should not encounter ELet here (should have been lifted)."
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
