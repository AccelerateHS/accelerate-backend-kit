 
--------------------------------------------------------------------------------
-- | Compiler pass to remove Array-level tuples entirely.
--------------------------------------------------------------------------------

-- TODO:
--  * Add copy-propagation to removeArrayTuple

module Data.Array.Accelerate.BackendKit.Phase1.RemoveArrayTuple 
       ( removeArrayTuple )
       where 

import Control.Monad
import Control.Applicative ((<$>))
import Prelude                                     hiding (sum)
import Control.Monad.State.Strict (State, evalState, get, put)
import Data.Map as M
import Data.List as L
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc  as S
import Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone as T

import Debug.Trace(trace)
-- tracePrint s x = trace (s ++ show x) x

--------------------------------------------------------------------------------
-- Types / Shorthands:
                 
type TAExp = T.AExp S.Type

type SubNameMap = M.Map S.Var [S.Var]
-- | A binding EITHER for a scalar or array variable:
type Binding  a = (S.Var, S.Type, a)
type Bindings a = [Binding a]
type FlexBindings = Bindings (Either T.Exp S.AExp)

type CollectM = State (Int, Bindings T.Exp)

-- A temporary tree datatype.  This is used internally in `removeArrayTuple`.
data TempTree a = TT (TempTree a) (TempTree a) [TempTree a] -- Internal node of degree two or more 
                | TLeaf a
  deriving Show                 

----------------------------------------------------------------------------------------------------
-- The pass itself:

-- | This removes the ArrayTuple and TupleRefFromRight syntactic
--   forms.  However, the final body may return more than one array
--   (i.e. an ArrayTuple), so the output must no longer be an expression
--   but a `Prog`.
-- 
--   This pass introduces new variable names and thus makes
--   assumptions about the naming convention.  It assumes that adding
--   "_N" suffixes to existing variables will not capture other existing
--   variables.       
-- 
--   This pass introduces new top-level scalar bindings to enable the
--   elimination of @ArrayTuple@s under @Cond@s.
--
--   Note that the input to this pass is in a "program like" (list of
--   top-level bindings) form rather than an expression form.  The
--   output is a final `S.Prog` value, which at this point becomes
--   /mandatory/ as a result of the added scalar bindings, which are
--   not representable within array expressions.
-- 
removeArrayTuple :: ([(S.Var, S.Type, TAExp)], TAExp) -> S.Prog ()
removeArrayTuple (binds, bod) = evalState main (0,[])
  where    
   main = do (newbinds,nameMap) <- doBinds [] M.empty binds
             newbod      <- dorhs nameMap bod
             newbinds2   <- dischargeNewScalarBinds
             let finalbinds = L.map (\ (v,t,x) -> S.ProgBind v t () x) $
                              mapBindings convertLeft (newbinds ++ newbinds2)
                 unVar (S.Vr v) = v
                 unVar x = error$ "removeArrayTuple: expecting the final result expressions "++
                                  "to be varrefs at this point, instead received: "++show x
             return $ S.Prog { progBinds   = finalbinds,
                               progResults = WithoutShapes (L.map unVar $ flattenTT newbod),
                               progType    = (getAnnot bod),
                               typeEnv     = M.fromList$ L.map (\(S.ProgBind v t _ _) -> (v,t)) finalbinds,
                               -- FIXME: variables have ALREADY been generated before
                               -- this point.  So we either need to push the tracking
                               -- of this EARLIER, *or* we need to count all the
                               -- variables in the program and set this number above them:
                               uniqueCounter = 0 }
 
   -- Called on already processed expressions:
   flattenTT :: TempTree S.AExp -> [S.AExp]
   flattenTT x =
     case x of      
       TLeaf e   -> [e]
       TT a b ls -> flattenTT a ++ flattenTT b ++
                    concatMap flattenTT ls

   -- | Apply a function to the RHS expression contained in each bind.  SYB stuff.
   mapBindings _ [] = []
   mapBindings fn ((v,t,x):tl) = (v,t,fn x) : mapBindings fn tl
--   mapBindings fn ((S.ProgBind v t d x) : tl) = S.ProgBind v t d (fn x) : mapBindings fn tl

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
   -- The resulting bindings bind finer granularity,
   -- post-detupling, "subnames".
   -- 
   -- We keep two accumulators: 
   --   * the first a list (for output) and 
   --   * the second a map (for fast access).
   doBinds :: FlexBindings -> SubNameMap -> [(S.Var, S.Type, TAExp)] 
           -> CollectM (FlexBindings,SubNameMap)
   doBinds acc macc [] = return (reverse acc, macc)
   doBinds acc macc ((vr,ty,rhs) :remaining) = do 
     rhs'       <- dorhs macc rhs     
     rhsScalars <- dischargeNewScalarBinds 
     
     let (macc',thisbnd) = 
           case L.map Right $ flattenTT rhs' of
             [ae] -> (macc, [(vr,ty,ae)]) -- No fresh names.
             unpacked -> 
               let subnames  = freshNames vr (length unpacked)
                   types     = deepDetupleTy ty
                   flattened = 
                     if length subnames == length types && 
                        length types    == length unpacked 
                     then zip3 subnames types unpacked 
                     else error$"Expected these to be the same length:\n"++
                          " Fresh names: "++show subnames++", types "++show types++" unpacked, "++show unpacked
               in (M.insert vr subnames macc, flattened)
     let acc'  = thisbnd ++ rhsScalars ++ acc
     doBinds acc' macc' remaining

   -- FIXME: use the genUnique library routine:
   freshNames vr len = L.map (S.var . ((show vr ++"_")++) . show) [1..len]

   -- Types are stored in natural Accelerate textual order:
   deTupleTy (S.TTuple ls) = ls
   deTupleTy oth           = [oth]
   deepDetupleTy (S.TTuple ls) = concatMap deTupleTy ls
   deepDetupleTy oth           = [oth]   
   
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
       T.Use ty arr                -> return$ TLeaf$ S.Use arr
       T.Generate aty ex fn        -> return$ TLeaf$ S.Generate (cE ex) (cF fn)
       T.ZipWith _ fn (T.Vr _ v1) (T.Vr _ v2)  -> lfr$ S.ZipWith (cF2 fn) v1 v2 
       T.Map     _ fn (T.Vr _ v)               -> lfr$ S.Map     (cF fn)  v
       T.Replicate aty slice ex (T.Vr _ v)     -> lfr$ S.Replicate slice (cE ex) v
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


----------------------------------------------------------------------------------------------------
-- Helper functions:

listToTT :: [TempTree a] -> TempTree a
listToTT [] = error "listToTT: We are only representing non-empty tuples of arrays here... looks like that's not good enough"
listToTT [x] = x 
listToTT (x:y:tl) = TT x y tl

listOfLeaves :: [a] -> TempTree a
listOfLeaves = listToTT . L.map TLeaf

-- Index from the right:
indexTT :: TempTree a -> Int -> TempTree a
indexTT _ i | i < 0 = error "indexTT: negative index not allowed"
indexTT (TLeaf x) 0 = TLeaf x 
indexTT (TLeaf x) i = error$"cannot index singleton tuple with index: "++show i
indexTT (TT a b rest) i = reverse (a:b:rest) !! i

fromLeaf :: Show t => TempTree t -> t
fromLeaf (TLeaf x) = x
fromLeaf oth = error$"fromLeaf: was expecting a TLeaf! "++show oth

-- TODO : Finish this.  

-- Trivial expressions can be duplicated and don't warrant introducing let bindings.
isTrivial :: T.Exp -> Bool
isTrivial (T.EVr _)    = True
isTrivial (T.EConst _) = True                     
isTrivial _            = False
-- This will pretty much always be false for any realistic Cond condition...

lf :: Functor f => f a -> f (TempTree a)
lf x = TLeaf <$> x

cE :: T.Exp -> S.Exp
lfr = lf . return

cE  = convertExps    
cF  = convertFun1
cF2 = convertFun2
