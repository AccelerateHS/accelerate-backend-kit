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
type Env  = M.Map C.Var ([C.Var], C.Type)

type TEnv = M.Map C.Var C.Type


----------------------------------------------------------------------------------------------------
-- First, a let-lifting pass that also lifts out conditional tests.
----------------------------------------------------------------------------------------------------

-- TODO: Use a better approach for coining fresh temporaries.  It
-- would help to form a Set of all existing variables, or to simply
-- keep a Map that freshens ids on the way down.

liftELets :: Env -> S.Exp -> State Int S.Exp
liftELets outerEnv orig = 
   return$ discharge $ loop plainTenv orig
 where
   plainTenv = M.map snd outerEnv   
   
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
   loopRHS :: TEnv -> S.Exp -> State (Bindings S.Exp) (S.Exp)
   loopRHS tenv ex = 
     case ex of
       -- Introduce a temporary for the test expression:
       S.ECond e1 e2 e3 -> do 
         let e2' = (discharge$ loop tenv e2) 
             e3' = (discharge$ loop tenv e3)
         -- Lift the test expression out only if necessary:           
         e1' <- if S.isTrivial e1 
                then return e1
                else liftOut C.TBool =<< loop tenv e1
         return $ S.ECond e1' e2' e3'
       
       oth -> loop tenv ex
     
   loop ::TEnv -> S.Exp -> State (Bindings S.Exp) (S.Exp)
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


-- Count the number of total variables in an expression.  This is used
-- as the basis for coining new unique identifiers.  IDEALLY ASTs
-- would keep this information around so that it doesn't need to be
-- recomputed.
countVars :: S.AExp C.Type -> Int
countVars orig = aexp orig
 where 
   exp :: S.Exp -> Int
   exp ex = 
    case ex of
      S.ELet (_,_,rhs) bod     -> 1 + exp rhs + exp bod
      S.EVr    _               -> 0
      S.EConst _               -> 0
      S.EShape avr             -> 0
      S.EShapeSize ex          -> exp ex
      S.ETuple ls              -> sum $ L.map exp ls
      S.EIndex ls              -> sum $ L.map exp ls
      S.EPrimApp ty p args     -> sum $ L.map exp args
      S.ETupProject ind len ex -> exp ex
      S.EIndexScalar avr ex    -> exp ex
      S.EIndexConsDynamic e1 e2 -> exp e1 + exp e2
      S.EIndexHeadDynamic e     -> exp e
      S.EIndexTailDynamic e     -> exp e
      S.ECond a b c             -> exp a + exp b + exp c

   fn1 (C.Lam1 _   bod) = exp bod
   fn2 (C.Lam2 _ _ bod) = exp bod

   aexp :: S.AExp C.Type -> Int
   aexp ae = 
     case ae of 
       S.Let _ (v,ty,rhs) bod -> aexp rhs + aexp bod
       S.Apply _ (C.Lam1 (v,ty) abod) ae -> aexp abod + aexp ae
       S.Vr _ _              -> 0
       S.Unit _ _            -> 0
       S.Use _ _             -> 0
       S.Generate _ _ _      -> 0
       S.ZipWith _ fn ae1 ae2 -> fn2 fn + aexp ae1 + aexp ae2
       S.Map     _ fn ae      -> fn1 fn + aexp ae
       S.TupleRefFromRight _ _ ae -> aexp ae
       S.Cond _ ex ae1 ae2        -> exp ex + aexp ae1 + aexp ae2
       S.Replicate _ _ ex ae -> exp ex + aexp ae
       S.Index     _ _ ae ex -> exp ex + aexp ae
       S.Fold  a fn einit ae         -> fn2 fn + exp einit + aexp ae
       S.Fold1 a fn       ae         -> fn2 fn +             aexp ae
       S.FoldSeg a fn einit ae aeseg -> fn2 fn + exp einit + aexp ae + aexp aeseg
       S.Fold1Seg a fn      ae aeseg -> fn2 fn +             aexp ae + aexp aeseg
       S.Scanl    a fn einit ae      -> fn2 fn + exp einit + aexp ae
       S.Scanl'   a fn einit ae      -> fn2 fn + exp einit + aexp ae
       S.Scanl1   a fn       ae      -> fn2 fn +             aexp ae
       S.Scanr    a fn einit ae      -> fn2 fn + exp einit + aexp ae
       S.Scanr'   a fn einit ae      -> fn2 fn + exp einit + aexp ae
       S.Scanr1   a fn       ae      -> fn2 fn +             aexp ae
       S.Permute a f2 ae1 f1 ae2 -> fn2 f2 + fn1 f1  + aexp ae1 + aexp ae2
       S.Backpermute a ex lam ae -> exp ex + fn1 lam + aexp ae
       S.Reshape     a ex     ae -> exp ex + aexp ae
       S.Stencil   a fn bndry ae -> fn1 fn + aexp ae
       S.Stencil2  a fn bnd1 ae1 bnd2 ae2 -> fn2 fn + aexp ae1 + aexp ae2
       S.ArrayTuple a aes -> sum $ L.map aexp aes
       

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
removeScalarTuple :: Env -> S.Exp -> State Int T.Block
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
