{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A few different passes for lowering the raw Acc-converted ASTs.


-- TODO:
--  * Add copy-propagation to removeArrayTuple

module Data.Array.Accelerate.SimplePasses.Lowering 
       (
         liftComplexRands,
         liftLets, 
         gatherLets,
         removeArrayTuple
         
         -- staticTuples -- Unfinished
       )
       where 

-- standard libraries
import Control.Monad
import Control.Applicative ((<$>),(<*>))
import Prelude                                     hiding (sum)
import Control.Monad.State.Strict (State, evalState, runState, get, put, modify)
import Data.Map as M
import Data.List as L
import Text.PrettyPrint.GenericPretty (Out(doc), Generic)
import Data.Array.Accelerate.SimpleAST   as S
import Data.Array.Accelerate.SimplePasses.IRTypes as T

import Debug.Trace(trace)
tracePrint s x = trace (s ++ show x) x

------------------------------------------------------------

-- TODO : Finish this.  

-- Trivial expressions can be duplicated and don't warrant introducing let bindings.
isTrivial (T.EVr _)    = True
isTrivial (T.EConst _) = True                     
isTrivial _            = False
-- This will pretty much always be false for any realistic Cond condition...

isAVar (T.Vr _ _)  = True
isAVar _           = False

--------------------------------------------------------------------------------
-- Compiler pass to complex operands into let bindings
--------------------------------------------------------------------------------

-- | Step one in a program flattening process.
-- 
-- The end goal is to flatten all nested array expressions such that
-- array arguments to all primitive forms are varrefs.  This pass
-- simply introduces Lets wherever a complex operand occurs.
-- Subsequent let lifting will achieve full flattening.
--        
-- This pass also ensures that the final body of the program is a
-- varref (i.e. it lifts the body as well).
liftComplexRands :: TAExp -> TAExp
liftComplexRands aex = 
    -- By starting off with 'flat' we ALSO lift the body of the whole program
    -- evalState (flat aex) (0,[])
    evalState (discharge (flat aex)) 0
  where  
   isVar :: TAExp -> Bool
   isVar aex = 
     case aex of 
       T.Vr _ _ -> True
       _        -> False
   flat :: TAExp -> State (Int,Bindings TAExp) TAExp 
   flat aex | isVar aex = return aex
   flat (T.Let rt (v,ty,rhs) bod) = do
     rhs' <- lift$ loop rhs
     bod' <- flat bod
     return$ T.Let rt (v,ty,rhs') bod'
   flat (T.Apply rt fn ae) = do -- Let's in disguise.
     let S.Lam1 (v,ty) abod = fn 
     rand' <- lift$ loop ae
     abod' <- flat abod
     return$ T.Apply rt (S.Lam1 (v,ty) abod') rand'
   -- Otherwise we lift it into a Let:
   flat aex = 
     do tmp <- tmpVar2
        let ty = getAnnot aex
        rhs' <- lift$ loop aex
        return$ T.Let ty (tmp,ty, rhs') (T.Vr ty tmp)
   
   tmpVar2 :: State (Int,Bindings TAExp) S.Var
   tmpVar2 = 
     do (cnt,ls) <- get 
        put (cnt+1, ls)
        return$ S.var $ "tmp_"++show cnt
   
   -- | Discharge the new bindings introduced by forming a Let.  This
   --   also processs all the RHS's of the new Let, which should be
   --   unprocessed at the point they are inserted in the state.
   discharge :: State (Int,Bindings TAExp) TAExp -> State Int TAExp
   discharge m = do
     cnt <- get
     let (ae, (cnt2, binds)) = runState m (cnt,[])
         rty = getAnnot ae
     put cnt2 
     let unroll []                = return ae
         unroll ((v,ty,rhs):rest) = T.Let rty . (v,ty,) <$> loop rhs <*> unroll rest
     unroll binds

   -- | Insert a dummy state to lift between monads.
   lift :: State Int a -> State (Int,Bindings TAExp) a
   lift m = do (cnt,ls) <- get
               let (x,cnt') = runState m cnt
               put (cnt',ls)
               return x

   -- There are some AExps buried within Exps.  This lifts them out,
   -- guaranting that only varrefs to array values will remain inside
   -- scalar expressions.  The AExp's returned are UNPROCESSED.
   exp :: T.Exp -> State (Int,Bindings TAExp) T.Exp
   exp e = 
     let 
         addbind :: TAExp -> State (Int,Bindings TAExp) S.Var
         addbind ae = do tmp <- tmpVar2
                         modify (\ (cnt,binds) -> (cnt, (tmp, getAnnot ae, ae) : binds))
                         return tmp
     in     
     case e of  
       -- For cleanliness we don't inject extra variable-variable copies:
       T.EShape       ae    | isAVar ae -> return e
       T.EIndexScalar ae ex | isAVar ae -> T.EIndexScalar ae <$> exp ex
       T.EIndexScalar ae ex -> do tmp <- addbind ae
                                  T.EIndexScalar (T.Vr (getAnnot ae) tmp) <$> exp ex
       T.EShape       ae    -> do tmp <- addbind ae
                                  return$ T.EShape (T.Vr (getAnnot ae) tmp)
       -- The rest is BOILERPLATE:
       ------------------------------------------------------------
       T.EVr vr                      -> return$ T.EVr vr
       T.EConst c                    -> return$ T.EConst c 
       T.ELet (vr,ty,rhs) bod        -> do rhs' <- exp rhs
                                           T.ELet (vr,ty, rhs') <$> exp bod
       T.EPrimApp ty p args          -> T.EPrimApp ty p <$> mapM exp args
       T.ECond e1 e2 e3              -> T.ECond      <$> exp e1 <*> exp e2 <*> exp e3 
       T.EShapeSize ex               -> T.EShapeSize <$> exp ex
       T.ETuple ls                   -> T.ETuple <$> mapM exp ls
       T.ETupProjectFromRight ind ex -> T.ETupProjectFromRight ind <$> exp ex
       T.EIndex els                  -> T.EIndex <$> mapM exp els
       T.EIndexConsDynamic e1 e2     -> T.EIndexConsDynamic <$> exp e1 <*> exp e2         
       T.EIndexHeadDynamic e         -> T.EIndexHeadDynamic <$> exp e
       T.EIndexTailDynamic e         -> T.EIndexTailDynamic <$> exp e

   cF  (S.Lam1 (v,ty)          bod) = S.Lam1 (v,ty)          <$> exp bod
   cF2 (S.Lam2 (v1,t1) (v2,t2) bod) = S.Lam2 (v1,t1) (v2,t2) <$> exp bod

   -- This has two jobs.
   --   (1) recur through `flat` so as to introduce lets.
   --   (2) lift let's out of Exps 
   -- To achieve (2) we must choose a place for the Let's.  We
   -- discharge them during each call to loop.  This should put the
   -- bindings directly around the array-level expression that uses
   -- them, but after (inside) any outer let bindings that might be referenced.
   loop :: TAExp -> State Int TAExp -- Keeps a counter.
   loop aex = discharge result
    where 
     result :: State (Int,Bindings TAExp) TAExp
     result = 
      -- This is 100% BOILERPLATE, except that we go through `flat` for most recursions.
      case aex of 
        T.Vr _ _              -> return aex
        T.Unit _ _            -> return aex
        T.Use _ _             -> return aex
        T.Generate _ _ _      -> return aex
        T.Let rt (v,ty,rhs) bod -> 
           do rhs' <- lift$ loop rhs -- Note: These calls to loop 
              bod' <- lift$ loop bod -- will discharge Exp-lifted lets. 
              return$ T.Let rt (v,ty,rhs') bod'
        T.Apply rt fn ae -> 
           do let S.Lam1 (v,ty) abod = fn 
              rand' <- lift$ loop ae
              abod' <- lift$ loop abod
              return$ T.Apply rt (S.Lam1 (v,ty) abod') rand'
        T.TupleRefFromRight a ind ae -> T.TupleRefFromRight a ind <$> flat ae             
        T.Index     a slc ae ex      -> T.Index a slc <$> flat ae <*> exp   ex
--        T.Index     a slc ae ex -> (\ ae' -> T.Index a slc ae' ex) <$> flat ae 
        T.ZipWith a fn2 ae1 ae2       -> T.ZipWith a <$> cF2 fn2  <*> flat ae1 <*> flat ae2
        T.Map     a fn ae             -> T.Map     a <$> cF fn    <*> flat ae
        T.Cond    a ex ae1 ae2        -> T.Cond    a <$> exp   ex <*> flat ae1 <*> flat ae2 
        T.Replicate a slice ex ae     -> T.Replicate a slice     <$> exp   ex  <*> flat ae
        T.Fold     a fn ein  ae       -> T.Fold     a <$> cF2 fn <*> exp   ein <*> flat ae
        T.FoldSeg  a fn ein  ae aeseg -> T.FoldSeg  a <$> cF2 fn <*> exp   ein <*> flat ae <*> flat aeseg
        T.Fold1    a fn      ae       -> T.Fold1    a <$> cF2 fn               <*> flat ae
        T.Fold1Seg a fn      ae aeseg -> T.Fold1Seg a <$> cF2 fn               <*> flat ae <*> flat aeseg
        T.Scanl    a fn ein  ae       -> T.Scanl    a <$> cF2 fn <*> exp   ein <*> flat ae  
        T.Scanl'   a fn ein  ae       -> T.Scanl'   a <$> cF2 fn <*> exp   ein <*> flat ae  
        T.Scanl1   a fn      ae       -> T.Scanl1   a <$> cF2 fn               <*> flat ae 
        T.Scanr    a fn ein  ae       -> T.Scanr    a <$> cF2 fn <*> exp   ein <*> flat ae 
        T.Scanr'   a fn ein  ae       -> T.Scanr'   a <$> cF2 fn <*> exp   ein <*> flat ae 
        T.Scanr1   a fn      ae       -> T.Scanr1   a <$> cF2 fn               <*> flat ae
        T.Permute  a fn ae1 fn1 ae2   -> T.Permute  a <$> cF2 fn <*> flat ae1  <*> cF fn1 <*> flat ae2
        T.Backpermute a ex lam ae    -> T.Backpermute a <$> exp   ex <*> cF lam <*> flat ae
        T.Reshape     a ex     ae    -> T.Reshape     a <$> exp   ex <*> flat ae
        T.Stencil   a fn bndry ae    -> T.Stencil     a <$> cF fn    <*> return bndry <*> flat ae
        T.Stencil2  a fn bnd1 ae1 bnd2 ae2 -> T.Stencil2 a <$> cF2 fn <*> return bnd1 <*> flat ae1 <*> return bnd2 <*> flat ae2
        T.ArrayTuple a aes                 -> T.ArrayTuple a <$> mapM flat aes

--------------------------------------------------------------------------------
-- Compiler pass to lift Lets
--------------------------------------------------------------------------------

-- | This pass lifts all Let bindings to the outside.  
-- 
--   @Apply@ also gets converted to @Let@ in this pass.
-- 
--   The resulting program will have a spine of Lets (with Let-free
--   RHS's) followed by a Let-free body.
liftLets :: T.AExp S.Type -> T.AExp S.Type
liftLets x = 
     if L.null binds then loop binds else
     trace ("[dbg] Lifted out "++show (length binds)++" Lets ...") $ loop binds
  where (binds, bod) = gatherLets x
        finalTy = getAnnot bod
        loop [] = bod
        loop (hd:tl) = T.Let finalTy hd $ loop tl

type TAExp = T.AExp S.Type

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


--------------------------------------------------------------------------------
-- Compiler pass to remove Array tuples
--------------------------------------------------------------------------------


type SubNameMap = M.Map S.Var [S.Var]
-- | A binding EITHER for a scalar or array variable:
type Binding  a = (S.Var, S.Type, a)
type Bindings a = [Binding a]
type FlexBindings = Bindings (Either T.Exp S.AExp)

type CollectM = State (Int, Bindings T.Exp)

-- A temporary tree datatype.  This is used internally in `removeArrayTuple`.
data TempTree a = TT (TempTree a) (TempTree a) [TempTree a] -- Node of degree two or more 
                | TLeaf a
  deriving Show                 

listToTT :: [TempTree a] -> TempTree a
listToTT [] = error "listToTT: We are only representing non-empty tuples of arrays here... looks like that's not good enough"
listToTT [x] = x 
listToTT (x:y:tl) = TT x y tl

listOfLeaves :: [a] -> TempTree a
listOfLeaves = listToTT . L.map TLeaf

-- Index from the right:
indexTT _ i | i < 0 = error "indexTT: negative index not allowed"
indexTT (TLeaf x) 0 = TLeaf x 
indexTT (TLeaf x) i = error$"cannot index singleton tuple with index: "++show i
indexTT (TT a b rest) i = reverse (a:b:rest) !! i

fromLeaf (TLeaf x) = x
fromLeaf oth = error$"fromLeaf: was expecting a TLeaf! "++show oth


-- | This removes ArrayTuple and TupleRefFromRight.  However, the
--   final body may return more than one array (i.e. an ArrayTuple),
--   so the output must no longer be an expression but a `Prog`.
-- 
--   This pass introduces new variable names and thus makes
--   assumptions about the naming convention.  It assumes that adding
--   "_N" suffixes to existing variables will not capture existing
--   variables.       
-- 
--   This pass introduces new top-level scalar bindings to enable the
--   elimination of @ArrayTuple@s under @Cond@s.
--
--   Note that the input to this pass is in a "program like" (list of
--   top-level bindings) form rather than an expression form.  The
--   output is a final `S.Prog` value, which at this point becomes
--   /mandatory/ as a result of the added scalar bindings, which are
--   not representable in the `AExp` types.
-- 
removeArrayTuple :: ([(S.Var, S.Type, TAExp)], TAExp) -> S.Prog
removeArrayTuple (binds, bod) = evalState main (0,[])
  where    
   main = do (newbinds,nameMap) <- doBinds [] M.empty binds
             newbod      <- dorhs nameMap bod
             newbinds2   <- dischargeNewScalarBinds
             let finalbinds = mapBindings convertLeft (newbinds ++ newbinds2)
                 unVar (S.Vr v) = v
                 unVar x = error$ "removeArrayTuple: expecting the final result expressions to be varrefs at this point, instead received: "++show x
             return $ S.Letrec finalbinds
                               (L.map unVar $ flattenTT newbod)
                               (getAnnot bod)
 
   -- Called on already processed expressions:
   flattenTT :: TempTree S.AExp -> [S.AExp]
   flattenTT x = 
     case x of      
       TLeaf e   -> [e]
       TT a b ls -> flattenTT a ++ flattenTT b ++
                    concatMap flattenTT ls
    
   mapBindings _ [] = []
   mapBindings fn ((v,t,x):tl) = (v,t,fn x) : mapBindings fn tl

   convertLeft (Left  ex)  = Left  $ convertExps  ex
   convertLeft (Right ae) = Right ae

   isTupledTy (TTuple _) = True
   isTupledTy _          = False

   dischargeNewScalarBinds :: CollectM FlexBindings
   dischargeNewScalarBinds = do 
     (cntr,newbinds) <- get 
     put (cntr,[])
     return$ L.map (\(v,t,r) -> (v,t, Left (r))) 
             newbinds

   -- This iterates over the bindings from top to bottom.  It ASSUMES
   -- that they are topologically sorted.  This way it can break up
   -- Conds as it goes, and rely on those results subsequently.
   -- 
   -- The resulting bindings bind the finer granularity,
   -- post-detupling, "subnames".
   -- 
   -- We keep two accumulators: 
   --   * the first a list (for output) and 
   --   * the second a map (for fast access).
   doBinds :: FlexBindings -> SubNameMap -> [(S.Var, S.Type, TAExp)] 
           -> CollectM (FlexBindings,SubNameMap)
   doBinds acc macc [] = return (reverse acc, macc)
   doBinds acc macc ((vr,ty,rhs) :remaining) = do 
     rhs' <- dorhs macc rhs     
     rhsScalars <- dischargeNewScalarBinds 
     
     let (macc',thisbnd) = 
           case L.map Right $ flattenTT rhs' of
             [ae] -> (macc, [(vr,ty,ae)]) -- No fresh names.
             unpacked -> 
               let subnames  = freshNames vr (length unpacked)
                   flattened = zip3 subnames (deTupleTy ty) unpacked 
               in (M.insert vr subnames macc, flattened)
     let acc'  = thisbnd ++ rhsScalars ++ acc
     doBinds acc' macc' remaining

   freshNames vr len = L.map (S.var . ((show vr ++"_")++) . show) [1..len]

   -- Types are stored in reverse order from natural Accelerate textual order:
   -- deTupleTy (S.TTuple ls) = concatMap deTupleTy (reverse ls)
   deTupleTy (S.TTuple ls) = reverse ls
   deTupleTy oth           = [oth]
   
   -- Process the right hand side of a binding, breakup up Conds and
   -- rewriting variable references to their new detupled targets.
   dorhs :: M.Map S.Var [S.Var] -> TAExp -> CollectM (TempTree S.AExp)
   -- The eenv here maps old names onto a list of new "subnames" for
   -- tuple components.  
   dorhs eenv aex = 
     case aex of
       
       -- Variable references to tuples need to be deconstructed.
       -- The original variable will disappear.
       T.Vr _ vr -> case M.lookup vr eenv of  
                     Just names -> return $ listToTT (L.map (TLeaf . S.Vr) names)
                     Nothing    -> return $ TLeaf (S.Vr vr)

       -- Have to consider flattening of nested array tuples here:
       -- T.ArrayTuple ls -> concatMap (dorhs eenv) $ ls
       T.ArrayTuple _ ls -> listToTT <$> mapM (dorhs eenv) ls      

       T.TupleRefFromRight _ ind ae -> do
         rhs' <- dorhs eenv ae
         return $ indexTT rhs' ind 

       -- Conditionals with tuples underneath need to be broken up:
       T.Cond ty ex ae1 ae2 | isTupledTy ty -> 
       -- Breaking up the conditional requires possibly let-binding the scalar expression:
         do 
            -- We split up the child expressions and add new bindings accordingly:
            ae1' <- dorhs eenv ae1
            ae2' <- dorhs eenv ae2                        
            
            (cntr,bnds) <- get
            let triv = isTrivial ex  
                fresh = S.var $ "cnd_" ++ show cntr
            -- Here we add the new binding, if needed:
            unless triv $ 
              put (cntr+1, (fresh,S.TBool,ex) : bnds)
--              put (cntr+1, [(fresh,S.TBool,ex)])
--              put (cntr+1, bnds ++ [(fresh,S.TBool,ex)])

            let 
                ex' = if triv then ex' else S.EVr fresh
                unVar (S.Vr v) = v
                unVar _ = error "Accelerate backend invariant-broken."
                ls1 = L.map unVar (flattenTT ae1') -- These must be fully flattened if there are nested tuples.
                ls2 = L.map unVar (flattenTT ae2')
                result = listOfLeaves $ L.map (uncurry $ S.Cond ex') (zip ls1 ls2)
            return result          

       T.Cond _ty ex (T.Vr _ v1) (T.Vr _ v2) -> 
--            return$ TLeaf$ S.Cond (cE ex) (fromLeaf (S.Vr v1) (fromLeaf (S.Vr v2)))
              return$ TLeaf$ S.Cond (cE ex) v1 v2
         
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       T.Unit _ty ex               -> return$ TLeaf$ S.Unit (cE ex)
       T.Use ty arr                -> return$ TLeaf$ S.Use ty arr
       T.Generate aty ex fn        -> return$ TLeaf$ S.Generate aty (cE ex) (cF fn)
       T.ZipWith _ fn (T.Vr _ v1) (T.Vr _ v2)  -> lfr$ S.ZipWith (cF2 fn) v1 v2 
       T.Map     _ fn (T.Vr _ v)               -> lfr$ S.Map     (cF fn)  v
       T.Replicate aty slice ex (T.Vr _ v)     -> lfr$ S.Replicate aty slice (cE ex) v
       T.Index     _ slc (T.Vr _ v) ex         -> lfr$ S.Index slc v (cE ex)
       T.Fold  _ fn einit (T.Vr _ v)           -> lfr$ S.Fold  (cF2 fn) (cE einit) v
       T.Fold1 _ fn       (T.Vr _ v)           -> lfr$ S.Fold1 (cF2 fn)            v
       T.FoldSeg _ fn einit (T.Vr _ v1) (T.Vr _ v2) -> lfr$ S.FoldSeg (cF2 fn) (cE einit) v1 v2
       T.Fold1Seg _ fn      (T.Vr _ v1) (T.Vr _ v2) -> lfr$ S.Fold1Seg (cF2 fn) v1 v2
       T.Scanl    _ fn einit (T.Vr _ v)        -> lfr$ S.Scanl    (cF2 fn) (cE einit) v
       T.Scanl'   _ fn einit (T.Vr _ v)        -> lfr$ S.Scanl'   (cF2 fn) (cE einit) v  
       T.Scanl1   _ fn       (T.Vr _ v)        -> lfr$ S.Scanl1   (cF2 fn)            v
       T.Scanr    _ fn einit (T.Vr _ v)        -> lfr$ S.Scanr    (cF2 fn) (cE einit) v
       T.Scanr'   _ fn einit (T.Vr _ v)        -> lfr$ S.Scanr'   (cF2 fn) (cE einit) v
       T.Scanr1   _ fn       (T.Vr _ v)         -> lfr$ S.Scanr1   (cF2 fn)            v
       T.Permute _ fn2 (T.Vr _ v1) fn1 (T.Vr _ v2) -> lfr$ S.Permute (cF2 fn2) v1 (cF fn1) v2
       T.Backpermute _ ex fn  (T.Vr _ v)     -> lfr$ S.Backpermute (cE ex) (cF fn) v
       T.Reshape     _ ex     (T.Vr _ v)     -> lfr$ S.Reshape     (cE ex)         v
       T.Stencil   _ fn bndry (T.Vr _ v)     -> lfr$ S.Stencil     (cF fn) bndry   v
       T.Stencil2  _ fn bnd1 (T.Vr _ v) bnd2 (T.Vr _ v2) -> lfr$ S.Stencil2 (cF2 fn) bnd1 v bnd2 v2
       T.Let _ _ _   -> error$ "removeArrayTuple: not expecting Let; should have been removed."
       T.Apply _ _ _ -> error$ "removeArrayTuple: not expecting Apply; should have been removed."
     
       oth -> error$"removeArrayTuple: this expression violated invariants: "++show oth


lf :: Functor f => f a -> f (TempTree a)
lf x = TLeaf <$> x
lfr = lf . return

cE  = convertExps    
cF  = convertFun1
cF2 = convertFun2

--------------------------------------------------------------------------------
-- Compiler pass to remove dynamic cons/head/tail on indices.
--------------------------------------------------------------------------------

-- UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED 

-- | This removes dynamic cons/head/tail on indices.  Indices are
--   plain tuples after this pass.
staticTuples :: TAExp -> TAExp
staticTuples ae = aexp M.empty ae
 where
--   aexp :: M.Map Var Int -> AExp -> [Builder]
   
   -- Trace the spine of lets.  We allow array tuples only at the very end:
   prog tenv aex = 
     case aex of 
       -- Lift out Let's as we encounter them:
       T.Let rt1 (v1,t1, T.Let rt2 (v2,t2,rhs) bod1) bod2 -> 
         -- NOTE: rt1 and rt2 should be equivalent:
         prog tenv $ T.Let rt1 (v2,t2,rhs) $
                     T.Let rt2 (v1,t1,bod1) bod2
       oth -> aexp tenv oth

   aexp tenv aex = 
     case aex of 
       
       -- Here we convert Apply to Let:
       T.Apply rty fn ae -> 
         T.Let rty (v,ty, aexp tenv' abod) (aexp tenv ae)
         where tenv' = M.insert v ty tenv         
               S.Lam1 (v,ty) abod = fn 
       
       -- TODO: Can we get rid of array tupling entirely?
       T.ArrayTuple rty aes -> T.ArrayTuple rty $ L.map (aexp tenv) aes       

       -- T.Let (vr,ty, T.ArrayTuple rhss) bod -> error "T.Let FINISHME"
         -- T.Let (vr,ty,loop rhs) (loop bod)
         -- where loop = aexp (M.insert vr ty tenv)

       -- The rest is BOILERPLATE; could scrap if we so chose:
       -------------------------------------------------------
       T.Vr rt vr -> T.Vr rt vr
       T.Let rt (vr,ty,rhs) bod -> T.Let rt (vr,ty,aexp tenv' rhs) (aexp tenv bod)
          where tenv' = M.insert vr ty tenv
       T.Unit rt ex -> T.Unit rt (exp tenv ex)
            
       T.Generate aty ex fn -> T.Generate aty (exp tenv ex) (lam1 tenv fn)
       T.ZipWith rt fn ae1 ae2 -> T.ZipWith rt (lam2 tenv fn) (aexp tenv ae1) (aexp tenv ae2)
       T.Map     rt fn ae      -> T.Map rt (lam1 tenv fn) (aexp tenv ae)

       T.TupleRefFromRight rt ind ae -> T.TupleRefFromRight rt ind (aexp tenv ae)

       T.Cond rt ex ae1 ae2 -> T.Cond rt (exp tenv ex) (aexp tenv ae1) (aexp tenv ae2)
       T.Use ty arr -> T.Use ty arr
 
       T.Replicate aty slice ex ae -> T.Replicate aty slice (exp tenv ex) (aexp tenv ae)
       T.Index     rt slc ae ex -> T.Index rt slc (aexp tenv ae) (exp tenv ex)
              
       T.Fold  rt fn einit ae         -> T.Fold  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Fold1 rt fn       ae         -> T.Fold1 rt (lam2 tenv fn) (aexp tenv ae)
       T.FoldSeg rt fn einit ae aeseg -> T.FoldSeg  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae) (aexp tenv aeseg)
       T.Fold1Seg rt fn      ae aeseg -> T.Fold1Seg rt (lam2 tenv fn) (aexp tenv ae) (aexp tenv aeseg)
       T.Scanl    rt fn einit ae      -> T.Scanl  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanl'   rt fn einit ae      -> T.Scanl' rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanl1   rt fn       ae      -> T.Scanl1 rt (lam2 tenv fn) (aexp tenv ae)
       T.Scanr    rt fn einit ae      -> T.Scanr  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanr'   rt fn einit ae      -> T.Scanr' rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanr1   rt fn       ae      -> T.Scanr1 rt (lam2 tenv fn) (aexp tenv ae)

       T.Permute rt fn2 ae1 fn1 ae2 -> 
         T.Permute rt (lam2 tenv fn2) (aexp tenv ae1) 
                      (lam1 tenv fn1) (aexp tenv ae2)

       T.Backpermute rt ex lam ae -> T.Backpermute rt (exp tenv ex) (lam1 tenv lam) (aexp tenv ae)
       T.Reshape     rt ex     ae -> T.Reshape     rt (exp tenv ex)                 (aexp tenv ae)
       T.Stencil   rt fn bndry ae -> T.Stencil     rt (lam1 tenv fn) bndry          (aexp tenv ae)
       T.Stencil2  rt fn bnd1 ae1 bnd2 ae2 ->  T.Stencil2 rt (lam2 tenv fn) bnd1 (aexp tenv ae1)
                                               bnd2 (aexp tenv ae2)
   -- Handle arity 1 lambdas:
   lam1 tenv (S.Lam1 (v,ty) bod) = S.Lam1 (v,ty) (exp tenv' bod)
     where tenv' = M.insert v ty tenv
   -- Handle arity 2 lambdas:
   lam2 tenv (S.Lam2 (v1,ty1) (v2,ty2) bod) = S.Lam2 (v1,ty1) (v2,ty2) (exp tenv' bod)
     where tenv' = M.insert v1 ty1 $ M.insert v2 ty2 tenv

   exp :: M.Map S.Var S.Type -> T.Exp -> T.Exp 
   exp tenv e = 
     case e of  
       -- T.EIndex els -> error "staticTupleIndices: EIndex is slated to be removed"

       -- -- TODO: Eliminate
       -- T.EIndexConsDynamic e1 e2 -> 
       --   -- This is potentially inefficient.
       --   error$"IndexCons - finish me"
         
       -- T.EIndexHeadDynamic e -> error "unimplemented: eliminate indexheaddynamic"
       -- T.EIndexTailDynamic e -> error "unimplemented: eliminate indextaildynamic"

       
       -- The rest is BOILERPLATE:
       ------------------------------------------------------------
       T.EVr vr -> T.EVr vr       
       T.ELet (vr,ty,rhs) bod -> T.ELet (vr,ty, exp tenv' rhs) (exp tenv bod)
         where tenv' = M.insert vr ty tenv
       T.EPrimApp ty p args -> T.EPrimApp ty p (L.map (exp tenv) args)
       T.ECond e1 e2 e3 -> T.ECond (exp tenv e1) (exp tenv e2) (exp tenv e3)
       T.EIndexScalar ae ex -> T.EIndexScalar (aexp tenv ae) (exp tenv ex)
       T.EShapeSize ex -> T.EShapeSize (exp  tenv ex)
       T.EShape     ae -> T.EShape     (aexp tenv ae)

       T.EConst c  -> T.EConst c 
       T.ETuple ls -> T.ETuple (L.map (exp tenv) ls)
       T.ETupProjectFromRight ind ex -> T.ETupProjectFromRight ind (exp tenv ex)
       
       T.EIndex els -> T.EIndex (L.map (exp tenv) els)
       T.EIndexConsDynamic e1 e2 -> T.EIndexConsDynamic (exp tenv e1) (exp tenv e2)
       T.EIndexHeadDynamic ex -> T.EIndexHeadDynamic (exp tenv ex)
       T.EIndexTailDynamic ex -> T.EIndexTailDynamic (exp tenv ex)

