       

module Data.Array.Accelerate.SimplePasses.LowerExps
       (removeScalarTuple)
       where

-- import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import qualified Data.Array.Accelerate.SimpleAST as S
import qualified Data.Array.Accelerate.FinalAST  as T
import           Data.Map                        as M
import           Data.List                       as L


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

type Binding  a = (S.Var, S.Type, a)
type Bindings a = [Binding a]

-- TODO - lifting pass

{-

liftLets :: T.AExp S.Type -> T.AExp S.Type
liftLets x = 
     if L.null binds then loop binds else
     trace ("[dbg] Lifted out "++show (length binds)++" Lets ...") $ loop binds
  where (binds, bod) = gatherLets x
        finalTy = getAnnot bod
        loop [] = bod
        loop (hd:tl) = T.Let finalTy hd $ loop tl


-- | Lift Let's upward, stopping only at conditionals.
gatherLets :: TAExp -> ([(S.Var, S.Type, TAExp)], TAExp)
gatherLets prog = (reverse binds, prog')
 where 
   (prog',binds) = runState (loop prog) [] 
   addbind bnd = do ls <- get; put (bnd:ls)
   
   loop :: TAExp -> State (Bindings TAExp) TAExp
   loop aex = 
     case aex of 
       T.Let _ (v,ty,rhs) bod -> 
          do rhs' <- loop rhs -- Important: Collect these bindings first.
             addbind (v,ty,rhs')
             loop bod
       -- We ALSO treat Apply's as Let bindings:
       T.Apply _ fn ae -> 
          do let S.Lam1 (v,ty) abod = fn 
             rhs' <- loop ae
             addbind (v,ty,rhs')
             loop abod
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       T.Vr _ _              -> return aex
       T.Unit _ _            -> return aex
       T.Use _ _             -> return aex
       T.Generate _ _ _      -> return aex
       T.ZipWith a fn ae1 ae2  -> T.ZipWith a fn <$> loop ae1 <*> loop ae2 
       T.Map     a fn ae       -> T.Map     a fn <$> loop ae
       T.TupleRefFromRight a ind ae -> T.TupleRefFromRight a ind <$> loop ae
       T.Cond a ex ae1 ae2     -> T.Cond a ex <$> loop ae1 <*> loop ae2 
       T.Replicate aty slice ex ae -> T.Replicate aty slice ex <$> loop ae
       T.Index     a slc ae ex -> (\ ae' -> T.Index a slc ae' ex) <$> loop ae
       T.Fold  a fn einit ae         -> T.Fold  a fn einit    <$> loop ae
       T.Fold1 a fn       ae         -> T.Fold1 a fn          <$> loop ae 
       T.FoldSeg a fn einit ae aeseg -> T.FoldSeg a fn einit  <$> loop ae <*> loop aeseg 
       T.Fold1Seg a fn      ae aeseg -> T.Fold1Seg a fn       <$> loop ae <*> loop aeseg 
       T.Scanl    a fn einit ae      -> T.Scanl    a fn einit <$> loop ae  
       T.Scanl'   a fn einit ae      -> T.Scanl'   a fn einit <$> loop ae  
       T.Scanl1   a fn       ae      -> T.Scanl1   a fn       <$> loop ae 
       T.Scanr    a fn einit ae      -> T.Scanr    a fn einit <$> loop ae 
       T.Scanr'   a fn einit ae      -> T.Scanr'   a fn einit <$> loop ae 
       T.Scanr1   a fn       ae      -> T.Scanr1   a fn       <$> loop ae
       T.Permute a fn2 ae1 fn1 ae2 -> (\ x y -> T.Permute a fn2 x fn1 y)
                                 <$> loop ae1 <*> loop ae2
       T.Backpermute a ex lam ae -> T.Backpermute a ex lam   <$> loop ae
       T.Reshape     a ex     ae -> T.Reshape     a ex       <$> loop ae
       T.Stencil   a fn bndry ae -> T.Stencil     a fn bndry <$> loop ae
       T.Stencil2  a fn bnd1 ae1 bnd2 ae2 -> (\ x y -> T.Stencil2 a fn bnd1 x bnd2 y) 
                                        <$> loop ae1 <*> loop ae2
       T.ArrayTuple a aes -> T.ArrayTuple a <$> mapM loop aes
-}

----------------------------------------------------------------------------------------------------


-- We map each identifier onto both a type and a list of finer-grained (post-detupling) names.
-- type Env = M.Map S.Var (S.Type, [S.Var])
type Env  = M.Map S.Var [S.Var]
type TEnv = M.Map S.Var S.Type

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
       S.EConst (S.Tup ls)  -> L.map T.EConst ls
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
                                   
       S.EIndexScalar avr ex -> [T.EIndexScalar avr (loop ex)]

       -- We know the dimensionality of arrays; further, shapes are just tuples so they are unpacked here:
       S.EShape avr | Just ty <- M.lookup avr tenv -> 
         L.map (`T.EProjFromShape` avr) $ 
         L.take (tupleNumLeaves ty) [0..]
                
       S.EShapeSize ex -> 
         -- To compute the size we simply generate a '+'-expression over all dimensions:
         [L.foldl1 (\ a b -> T.EPrimApp S.TInt (S.NP S.Add) [a,b]) (loop ex)]
   where 
      loop = exp env tenv
      loop1 e = case loop e of 
                 [x] -> x
                 ls  -> error$"removeScalarTuple: Expecting one value in this context, received: "++show ls
      isVar (S.EVr _) = True
      isVar _         = False
      isTupleVar vr = case M.lookup vr env of 
                        Nothing  -> error$"unbound variable!: "++show vr
                        Just [x] -> False
                        Just []  -> False
                        _        -> True


tupleNumLeaves :: S.Type -> Int
tupleNumLeaves (S.TTuple ls) = L.sum $ L.map tupleNumLeaves ls
tupleNumLeaves _             = 1
