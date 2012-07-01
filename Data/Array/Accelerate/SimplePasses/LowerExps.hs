{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}       

module Data.Array.Accelerate.SimplePasses.LowerExps
       (liftELets, removeScalarTuple)
       where

-- import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import Data.Array.Accelerate.SimplePasses.IRTypes as S
import qualified Data.Array.Accelerate.SimpleAST  as T
import qualified Data.Array.Accelerate.SimpleAST  as C
import           Data.Map                         as M
import           Data.List                        as L

import Control.Monad.State.Strict (StateT, State, runStateT, runState, get, put, lift)
import Control.Monad (mapM, (=<<))
import Control.Applicative ((<$>))

type Binding  a = (C.Var, C.Type, a)
type Bindings a = [Binding a]

-- We map each identifier onto both a type and a list of finer-grained (post-detupling) names.
type Env  = M.Map C.Var ([C.Var], C.Type)

type TEnv = M.Map C.Var C.Type


----------------------------------------------------------------------------------------------------
-- First, a let-lifting pass that also lifts out conditional tests.
----------------------------------------------------------------------------------------------------

-- TODO: Use a better approach for coining fresh temporaries.  It
-- would help to form a Set of all existing variables, or to simply
-- keep a Map that freshens ids on the way down.

-- type BindingAccM a = State (Bindings S.Exp) a
-- type BindingAccM a = StateT (Bindings S.Exp) (Identity) a
type BindingAccM a = StateT (Bindings S.Exp) (State Int) a

liftELets :: Env -> S.Exp -> State Int S.Exp
liftELets outerEnv orig = 
   discharge $ loop plainTenv orig
 where
   plainTenv = M.map snd outerEnv   
   
   addbind bnd = do ls <- get; put (bnd:ls)   
   discharge m = do (x,bnds) <- runStateT m []
                    return (unpack (reverse bnds) x)
   unpack [] x = x
   unpack (bnd:rst) x = S.ELet bnd (unpack rst x)
   
   isLet (S.ELet _ _) = True
   isLet _            = False

   liftOut :: C.Type -> S.Exp -> BindingAccM (S.Exp)
   liftOut ty rhs = do
     tmp <- lift $ mkTmp "tmpLEL"
     addbind (tmp,ty,rhs)
     return (S.EVr tmp)

   -- The rules are different for what is allowed in a Let-RHS:
   loopRHS :: TEnv -> S.Exp -> BindingAccM (S.Exp)
   loopRHS tenv ex = 
     case ex of
       -- Introduce a temporary for the test expression:
       S.ECond e1 e2 e3 -> do 
         e2' <- lift (discharge$ loop tenv e2) 
         e3' <- lift (discharge$ loop tenv e3)
         -- Lift the test expression out only if necessary:           
         e1' <- if S.isTrivial e1 
                then return e1
                else liftOut C.TBool =<< loop tenv e1
         return $ S.ECond e1' e2' e3'
       
       oth -> loop tenv ex
     
   loop ::TEnv -> S.Exp -> BindingAccM (S.Exp)
   loop tenv ex = 
     case ex of 

       S.ELet (v,ty,rhs) bod -> 
          do rhs' <- loopRHS tenv rhs -- Important: Collect these bindings first.
             addbind (v,ty,rhs')
             loop (M.insert v ty tenv) bod       
       
       S.ECond _ _ _ -> do 
         rhs@(S.ECond _ e2 e3) <- loopRHS tenv ex
         -- If either of the branches is a let this conditional must itself occur in a Let-RHS.
         if isLet e2 || isLet e3 
           then liftOut (retrieveExpType tenv rhs) rhs
           else return rhs
         
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       S.EVr    _               -> return ex
       S.EConst _               -> return ex
       S.EShape avr             -> return ex
       S.EShapeSize ex          -> S.EShapeSize <$> loop tenv ex
       S.ETuple ls              -> S.ETuple <$> mapM (loop tenv) ls
       S.EIndex ls              -> S.EIndex <$> mapM (loop tenv) ls
       S.EPrimApp ty p args     -> S.EPrimApp ty p <$> mapM (loop tenv) args
       S.ETupProject ind len ex -> S.ETupProject ind len <$> loop tenv ex
       S.EIndexScalar avr ex    -> S.EIndexScalar avr    <$> loop tenv ex
       
       S.EIndexConsDynamic _ _ -> error$"liftELets: no dynamic indexing at this point"
       S.EIndexHeadDynamic _   -> error$"liftELets: no dynamic indexing at this point"
       S.EIndexTailDynamic _   -> error$"liftELets: no dynamic indexing at this point"
       

----------------------------------------------------------------------------------------------------
-- After lifting this pass can remove tuples and make shape representations explicit.
----------------------------------------------------------------------------------------------------

type TmpM a = State Int a 

mkTmp :: Show a => a -> TmpM C.Var
mkTmp root = do n <- get; put (n+1)
                return $ C.var (show root ++"_"++ show n)


-- | This is not a full pass, rather just a function for converting expressions.
--   This is currently [2012.06.27] used by removeArrayTuple.
--       
--   This pass takes a type environment as argument.
--   It uses a state monad to access a counter for unique variable generation.
removeScalarTuple :: Env -> S.Exp -> TmpM T.Block
removeScalarTuple eenv expr = 
  stmt eenv expr
 where 
  -- Here we touch the outer parts of the expression tree,
  -- transforming it into statement blocks.  This depends critically
  -- on Let's having been lifted.
  stmt :: Env -> S.Exp -> State Int T.Block
  stmt env e = 
     case e of  
       -- Here's where we need to split up a binding into a number of new temporaries:
       S.ELet (vr,ty,rhs) bod -> do
           let tys   = C.flattenTupleTy ty
           tmps <- case tys of 
                     [_] -> return [vr]
                     _   -> mapM (mkTmp . const vr) tys
           let env'  = M.insert vr (tmps,ty) env
               -- Here we need to know that Let's have already been lifted out of the RHS to call exp:
               rhs'  = exp env rhs 
           case rhs of 
             S.ECond a b c -> do
               conseq <- stmt env b 
               altern <- stmt env c 
               let S.EVr vr = a               
               T.BMultiLet (tmps, tys, T.BCond vr conseq altern) <$>
                 stmt env' bod

             _ -> do bod' <- stmt env' bod
                     return $ L.foldr T.BLet bod' (zip3 tmps tys rhs')
       
       oth -> return $ T.BResults (exp env oth)
    where loop = stmt env

  -- Here we traverse the expression to remove tuples.
  exp :: Env -> S.Exp -> [T.Exp]
  exp env e = 
     case e of  
       
       S.EVr vr | Just (ls,_) <- M.lookup vr env -> L.map T.EVr ls
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

       -- (1) we know the dimensionality of arrays, and 
       -- (2) shapes are just tuples in our encoding.
       -- Therefore we can unpack them here:
       S.EShape (S.Vr _ avr) | Just (_,ty) <- M.lookup avr env -> 
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
      loop = exp env 
      loop1 e = case loop e of 
                 [x] -> x
                 ls  -> error$"removeScalarTuple: Expecting one value in this context, received: "++show ls

----------------------------------------------------------------------------------------------------
-- Helpers
                        
tupleNumLeaves :: C.Type -> Int
tupleNumLeaves (C.TTuple ls) = L.sum $ L.map tupleNumLeaves ls
tupleNumLeaves _             = 1
