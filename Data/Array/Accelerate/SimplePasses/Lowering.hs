
-- | A few different passes for lowering the raw Acc-converted ASTs.


-- TODO:
--  * Add copy-propagation to removeArrayTuple

module Data.Array.Accelerate.SimplePasses.Lowering 
       (
         liftLets, gatherLets,
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

import Debug.Trace(trace)
tracePrint s x = trace (s ++ show x) x

------------------------------------------------------------

-- TODO : Finish this.  

-- Trivial expressions can be duplicated and don't warrant introducing let bindings.
isTrivial (S.EVr _)    = True
isTrivial (S.EConst _) = True                     
isTrivial _            = False
-- This will pretty much always be false for any realistic Cond condition...

--------------------------------------------------------------------------------
-- Compiler pass to lift Lets
--------------------------------------------------------------------------------

-- | This pass lifts all Let bindings to the outside.  
-- 
--   @Apply@ also gets converted to @Let@ in this pass.
-- 
--   The resulting program will have a spine of Lets (with Let-free
--   RHS's) followed by a Let-free body.
liftLets :: S.AExp -> S.AExp
liftLets x = 
     if L.null binds then loop binds else
     trace ("[dbg] Lifted out "++show (length binds)++" Lets ...") $ loop binds
  where (binds, bod) = gatherLets x
        loop [] = bod
        loop (hd:tl) = S.Let hd $ loop tl

gatherLets :: S.AExp -> ([(S.Var, S.Type, S.AExp)], S.AExp)
gatherLets prog = (reverse binds, prog')
 where 
   (prog',binds) = runState (loop prog) [] 
   addbind bnd = do ls <- get; put (bnd:ls)
   loop :: S.AExp -> State [(S.Var, S.Type, S.AExp)] S.AExp
   loop aex = 
     case aex of 
       S.Let (v,ty,rhs) bod -> 
          do rhs' <- loop rhs -- Important: Collect these bindings first.
             addbind (v,ty,rhs')
             loop bod
       S.Apply fn ae -> 
          do let S.ALam (v,ty) abod = fn 
             rhs' <- loop ae
             addbind (v,ty,rhs')
             loop abod
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       S.Vr vr               -> return aex
       S.Unit ex             -> return aex
       S.Use ty arr          -> return aex
       S.Generate aty ex fn  -> return aex
       S.ZipWith fn ae1 ae2  -> S.ZipWith fn <$> loop ae1 <*> loop ae2 
       S.Map     fn ae       -> S.Map     fn <$> loop ae
       S.TupleRefFromRight ind ae -> S.TupleRefFromRight ind <$> loop ae
       S.Cond ex ae1 ae2     -> S.Cond ex <$> loop ae1 <*> loop ae2 
       S.Replicate aty slice ex ae -> S.Replicate aty slice ex <$> loop ae
       S.Index     slc ae ex -> (\ ae' -> S.Index slc ae' ex) <$> loop ae
       S.Fold  fn einit ae         -> S.Fold  fn einit    <$> loop ae
       S.Fold1 fn       ae         -> S.Fold1 fn          <$> loop ae 
       S.FoldSeg fn einit ae aeseg -> S.FoldSeg fn einit  <$> loop ae <*> loop aeseg 
       S.Fold1Seg fn      ae aeseg -> S.Fold1Seg fn       <$> loop ae <*> loop aeseg 
       S.Scanl    fn einit ae      -> S.Scanl    fn einit <$> loop ae  
       S.Scanl'   fn einit ae      -> S.Scanl'   fn einit <$> loop ae  
       S.Scanl1   fn       ae      -> S.Scanl1   fn       <$> loop ae 
       S.Scanr    fn einit ae      -> S.Scanr    fn einit <$> loop ae 
       S.Scanr'   fn einit ae      -> S.Scanr'   fn einit <$> loop ae 
       S.Scanr1   fn       ae      -> S.Scanr1   fn       <$> loop ae
       S.Permute fn2 ae1 fn1 ae2 -> (\ a b -> S.Permute fn2 a fn1 ae2)
                                 <$> loop ae1 <*> loop ae2
       S.Backpermute ex lam ae -> S.Backpermute ex lam   <$> loop ae
       S.Reshape     ex     ae -> S.Reshape     ex       <$> loop ae
       S.Stencil   fn bndry ae -> S.Stencil     fn bndry <$> loop ae
       S.Stencil2  fn bnd1 ae1 bnd2 ae2 -> (\ a b -> S.Stencil2 fn bnd1 a bnd2 b) 
                                        <$> loop ae1 <*> loop ae2
       S.ArrayTuple aes -> S.ArrayTuple <$> mapM loop aes


--------------------------------------------------------------------------------
-- Compiler pass to remove Array tuples
--------------------------------------------------------------------------------

type SubNameMap = M.Map S.Var [S.Var]
-- | A binding EITHER for a scalar or array variable:
type FlexBinding = (S.Var, S.Type, Either S.Exp S.AExp)

type CollectM = State (Int,[(S.Var,S.Type,S.Exp)])

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
removeArrayTuple :: ([(S.Var, S.Type, S.AExp)], S.AExp) -> S.Prog
removeArrayTuple (binds, bod) = evalState main (0,[])
  where    
   main = do (newbinds,nameMap) <- doBinds [] M.empty binds
             newbod    <- dorhs nameMap bod
             newbinds2 <- dischargeNewScalarBinds
             return $ S.Letrec (newbinds ++ newbinds2)
                               (deepDeTuple nameMap newbod) 
--                               (deTuple nameMap newbod)
                               (S.TTuple [])
 
   -- Called on already processed expressions:
   deepDeTuple eenv ae = 
     case ae of      
       S.ArrayTuple ls   -> concatMap (deepDeTuple eenv) ls
       oth -> [oth]
    
   origenv = M.fromList $ L.map (\ (a,b,c) -> (a,c)) binds

   -- Is a variable bound to an ArrayTuple?
   isTupledVar :: S.Var -> Bool
   isTupledVar vr = loop (origenv M.! vr)
     where 
       strictAnd True  True  = True
       strictAnd False False = False
       strictAnd x     y     = error$"isTupledVar: expecting var "++show vr
                               ++" to be bound to a tuple in both sides of the conditional" 
       loop x =
         case x of 
           S.Vr v2          -> isTupledVar v2
           S.ArrayTuple ls  -> True
           S.Cond _ ae1 ae2 -> loop ae1 `strictAnd` loop ae2
           _                -> False
   
   isTupled (S.ArrayTuple _) = True
   isTupled (S.Vr vr)        = isTupledVar vr
   isTupled  _               = False

   dischargeNewScalarBinds = do 
     (cntr,newbinds) <- get 
     put (cntr,[])
     return$ L.map (\(v,t,r) -> (v,t, Left r)) newbinds

   -- This iterates over the bindings from top to bottom.  It ASSUMES
   -- that they are topologically sorted.  This way it can break up
   -- Conds as it goes, and rely on those results subsequently.
   -- 
   -- We keep two accumulators, the first a list (for output) and the
   -- second a map (for fast access).
   doBinds :: [FlexBinding] -> SubNameMap -> [(S.Var, S.Type, S.AExp)] 
           -> CollectM ([FlexBinding],SubNameMap)
   doBinds acc macc [] = return (reverse acc, macc)
   doBinds acc macc ((vr,ty,rhs) :remaining) = do 
     rhs' <- dorhs macc rhs     
     rhsScalars <- dischargeNewScalarBinds 
     let unpacked  = L.map Right$ deTuple macc rhs'
         subnames  = freshNames vr (length unpacked)
         flattened = zip3 subnames (deTupleTy ty) unpacked 
         (macc',thisbnd) = 
           if length subnames > 1 
           then (M.insert vr subnames macc, flattened)
           else (macc, [(vr,ty,Right rhs')])
         acc'  = rhsScalars ++ thisbnd ++ acc
     doBinds acc' macc' remaining

   freshNames vr len = L.map (S.var . ((show vr ++"_")++) . show) [1..len]

   -- Unpack the bindings in the same (topologically sorted) order they originally occurred.
   unpackInOrder mp [] = []
   unpackInOrder mp ((vr,_,_):tl) = mp M.! vr : unpackInOrder mp tl

   -- Unpack an expression representing a known tuple.  AFTER Conds
   -- are broken up such an expression will have a very transparent
   -- form.
   deTuple eenv ae = 
     case ae of 
       -- The builtin operators (e.g. Fold) do NOT return tuples.
       -- Tuples can only take one of two forms at this point:
       S.ArrayTuple ls   -> ls
       S.Vr vr -> 
         case M.lookup vr eenv of 
           Just newNames -> L.map S.Vr newNames
           Nothing -> error$"removeArrayTuple: variable not bound at this point: "++show vr
       oth -> [oth]
       
   -- Types are stored in reverse order from natural Accelerate textual order:
   -- deTupleTy (S.TTuple ls) = concatMap deTupleTy (reverse ls)
   deTupleTy (S.TTuple ls) = reverse ls
   deTupleTy oth           = [oth]

   -- For array expressions that we know are not tuples:
   arrayonly eenv aex = 
     case aex of 
       S.ArrayTuple ls -> error$"removeArrayTuple: encountered ArrayTuple that was not on the RHS of a Let:\n"++show(doc aex)
       S.Cond ex ae1 ae2 -> S.Cond ex <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
       oth -> dorhs eenv oth
   
   -- Process the right hand side of a binding, breakup up Conds and
   -- rewriting variable references to their new detupled targets.
   dorhs :: M.Map S.Var [S.Var] -> S.AExp -> CollectM S.AExp
   -- The eenv here maps old names onto a list of new "subnames" for
   -- tuple components.  
   dorhs eenv aex = 
     case aex of 
       
       -- Variable references to tuples need to be deconstructed.
       -- The original variable will disappear.
       S.Vr vr -> case M.lookup vr eenv of  
                    Just names -> return $ mkArrayTuple (L.map S.Vr names)
                    Nothing    -> return aex
       
       -- Have to consider flattening of nested array tuples here:
       -- S.ArrayTuple ls -> concatMap (dorhs eenv) $ ls
       S.ArrayTuple ls -> S.ArrayTuple <$> mapM (dorhs eenv) ls 
       
       -- S.TupleRefFromRight ind ae | not (isTupled ae) -> 
       --   error "removeArrayTuple: TupleRefFromRight with unexpected input: "++show ae
       S.TupleRefFromRight ind ae -> do
         rhs' <- dorhs eenv ae
         return $ reverse (deTuple eenv rhs') !! ind
       
       -- Conditionals with tuples underneath need to be broken up:
       S.Cond ex ae1 ae2 | isTupled aex ->         
         -- Breaking up the conditional requires possibly let-binding the scalar expression:
         do 
            ae1' <- dorhs eenv ae1
            ae2' <- dorhs eenv ae2
            (cntr,bnds) <- get
            let triv = isTrivial ex  
            unless triv $ put (cntr+1, bnds)
            let fresh = S.var $ "cnd_" ++ show cntr
                ex' = if triv then ex' else S.EVr fresh
                ls1 = deTuple eenv ae1'
                ls2 = deTuple eenv ae2'
                result = mkArrayTuple $ L.map (uncurry $ S.Cond ex') (zip ls1 ls2)
            -- Here we add the new binding, if needed:
            let fakeType = trace "WARNING - REPLACE THIS WITH A REAL TYPE" (S.TTuple [])
            unless triv $ modify (\ (c,ls) -> (c, (fresh,fakeType,ex):ls))
            return result          
       
       S.Cond ex ae1 ae2 -> S.Cond ex <$> dorhs eenv ae1 <*> dorhs eenv ae2
       
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       S.Unit ex                   -> return aex
       S.Use ty arr                -> return aex
       S.Generate aty ex fn        -> return aex
       S.ZipWith fn ae1 ae2        -> S.ZipWith fn <$> arrayonly eenv ae1 <*> arrayonly eenv ae2 
       S.Map     fn ae             -> S.Map     fn <$> arrayonly eenv ae
       S.TupleRefFromRight ind ae  -> S.TupleRefFromRight ind <$> arrayonly eenv ae
       S.Cond ex ae1 ae2           -> S.Cond ex <$> arrayonly eenv ae1 <*> arrayonly eenv ae2 
       S.Replicate aty slice ex ae -> S.Replicate aty slice ex <$> arrayonly eenv ae
       S.Index     slc ae    ex    -> (\ ae' -> S.Index slc ae' ex) <$> arrayonly eenv ae
       S.Fold  fn einit ae         -> S.Fold  fn einit    <$> arrayonly eenv ae
       S.Fold1 fn       ae         -> S.Fold1 fn          <$> arrayonly eenv ae 
       S.FoldSeg fn einit ae aeseg -> S.FoldSeg fn einit  <$> arrayonly eenv ae <*> arrayonly eenv aeseg 
       S.Fold1Seg fn      ae aeseg -> S.Fold1Seg fn       <$> arrayonly eenv ae <*> arrayonly eenv aeseg 
       S.Scanl    fn einit ae      -> S.Scanl    fn einit <$> arrayonly eenv ae  
       S.Scanl'   fn einit ae      -> S.Scanl'   fn einit <$> arrayonly eenv ae  
       S.Scanl1   fn       ae      -> S.Scanl1   fn       <$> arrayonly eenv ae 
       S.Scanr    fn einit ae      -> S.Scanr    fn einit <$> arrayonly eenv ae 
       S.Scanr'   fn einit ae      -> S.Scanr'   fn einit <$> arrayonly eenv ae 
       S.Scanr1   fn       ae      -> S.Scanr1   fn       <$> arrayonly eenv ae
       S.Permute fn2 ae1 fn1 ae2   -> (\ a b -> S.Permute fn2 a fn1 ae2)
                                   <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
       S.Backpermute ex lam ae     -> S.Backpermute ex lam   <$> arrayonly eenv ae
       S.Reshape     ex     ae     -> S.Reshape     ex       <$> arrayonly eenv ae
       S.Stencil   fn bndry ae     -> S.Stencil     fn bndry <$> arrayonly eenv ae
       S.Stencil2  fn bnd1 ae1 bnd2 ae2 -> (\ a b -> S.Stencil2 fn bnd1 a bnd2 b) 
                                        <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
    
mkArrayTuple [one] = one
mkArrayTuple ls    = S.ArrayTuple ls

--------------------------------------------------------------------------------
-- Compiler pass to remove dynamic cons/head/tail on indices.
--------------------------------------------------------------------------------

-- UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED 

-- | This removes dynamic cons/head/tail on indices.  Indices are
--   plain tuples after this pass.
staticTuples :: S.AExp -> S.AExp
staticTuples ae = aexp M.empty ae
 where
--   aexp :: M.Map Var Int -> AExp -> [Builder]
   
   -- Trace the spine of lets.  We allow array tuples only at the very end:
   prog tenv aex = 
     case aex of 
       -- Lift out Let's as we encounter them:
       S.Let (v1,t1, S.Let (v2,t2,rhs) bod1) bod2 -> 
         prog tenv $ S.Let (v2,t2,rhs) $
                     S.Let (v1,t1,bod1) bod2


--       S.Let (vr,ty,rhs) bod -> S.Let (vr,ty,aexp tenv' rhs) (tail tenv bod)
--          where tenv' = M.insert vr ty tenv
       oth -> aexp tenv oth

   aexp tenv aex = 
     case aex of 
       
       -- Here we convert Apply to Let:
       S.Apply fn ae -> 
         S.Let (v,ty, aexp tenv' abod) (aexp tenv ae)
         where tenv' = M.insert v ty tenv         
               S.ALam (v,ty) abod = fn 
       
       -- TODO: Can we get rid of array tupling entirely?
       S.ArrayTuple aes -> S.ArrayTuple $ L.map (aexp tenv) aes       

       -- S.Let (vr,ty, S.ArrayTuple rhss) bod -> error "S.Let FINISHME"
         -- S.Let (vr,ty,loop rhs) (loop bod)
         -- where loop = aexp (M.insert vr ty tenv)

       -- The rest is BOILERPLATE; could scrap if we so chose:
       -------------------------------------------------------
       S.Vr vr -> S.Vr vr
       S.Let (vr,ty,rhs) bod -> S.Let (vr,ty,aexp tenv' rhs) (aexp tenv bod)
          where tenv' = M.insert vr ty tenv
       S.Unit ex -> S.Unit (exp tenv ex)
            
       S.Generate aty ex fn -> S.Generate aty (exp tenv ex) (lam1 tenv fn)
       S.ZipWith fn ae1 ae2 -> S.ZipWith (lam2 tenv fn) (aexp tenv ae1) (aexp tenv ae2)
       S.Map     fn ae      -> S.Map (lam1 tenv fn) (aexp tenv ae)

       S.TupleRefFromRight ind ae -> S.TupleRefFromRight ind (aexp tenv ae)

       S.Cond ex ae1 ae2 -> S.Cond (exp tenv ex) (aexp tenv ae1) (aexp tenv ae2)
       S.Use ty arr -> S.Use ty arr
 
       S.Replicate aty slice ex ae -> S.Replicate aty slice (exp tenv ex) (aexp tenv ae)
       S.Index     slc ae ex -> S.Index slc (aexp tenv ae) (exp tenv ex)
              
       S.Fold  fn einit ae         -> S.Fold  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       S.Fold1 fn       ae         -> S.Fold1 (lam2 tenv fn) (aexp tenv ae)
       S.FoldSeg fn einit ae aeseg -> S.FoldSeg  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae) (aexp tenv aeseg)
       S.Fold1Seg fn      ae aeseg -> S.Fold1Seg (lam2 tenv fn) (aexp tenv ae) (aexp tenv aeseg)
       S.Scanl    fn einit ae      -> S.Scanl  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       S.Scanl'   fn einit ae      -> S.Scanl' (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       S.Scanl1   fn       ae      -> S.Scanl1 (lam2 tenv fn) (aexp tenv ae)
       S.Scanr    fn einit ae      -> S.Scanr  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       S.Scanr'   fn einit ae      -> S.Scanr' (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       S.Scanr1   fn       ae      -> S.Scanr1 (lam2 tenv fn) (aexp tenv ae)

       S.Permute fn2 ae1 fn1 ae2 -> 
         S.Permute (lam2 tenv fn2) (aexp tenv ae1) 
                   (lam1 tenv fn1) (aexp tenv ae2)

       S.Backpermute ex lam ae -> S.Backpermute (exp tenv ex) (lam1 tenv lam) (aexp tenv ae)
       S.Reshape     ex     ae -> S.Reshape     (exp tenv ex)                 (aexp tenv ae)
       S.Stencil   fn bndry ae -> S.Stencil     (lam1 tenv fn) bndry          (aexp tenv ae)
       S.Stencil2  fn bnd1 ae1 bnd2 ae2 ->  S.Stencil2 (lam2 tenv fn) bnd1 (aexp tenv ae1)
                                                                      bnd2 (aexp tenv ae2)
   -- Handle arity 1 lambdas:
   lam1 tenv (S.Lam1 (v,ty) bod) = S.Lam1 (v,ty) (exp tenv' bod)
     where tenv' = M.insert v ty tenv
   -- Handle arity 2 lambdas:
   lam2 tenv (S.Lam2 (v1,ty1) (v2,ty2) bod) = S.Lam2 (v1,ty1) (v2,ty2) (exp tenv' bod)
     where tenv' = M.insert v1 ty1 $ M.insert v2 ty2 tenv

   exp :: M.Map S.Var S.Type -> S.Exp -> S.Exp 
   exp tenv e = 
     case e of  
       -- S.EIndex els -> error "staticTupleIndices: EIndex is slated to be removed"

       -- -- TODO: Eliminate
       -- S.EIndexConsDynamic e1 e2 -> 
       --   -- This is potentially inefficient.
       --   error$"IndexCons - finish me"
         
       -- S.EIndexHeadDynamic e -> error "unimplemented: eliminate indexheaddynamic"
       -- S.EIndexTailDynamic e -> error "unimplemented: eliminate indextaildynamic"

       
       -- The rest is BOILERPLATE:
       ------------------------------------------------------------
       S.EVr vr -> S.EVr vr       
       S.ELet (vr,ty,rhs) bod -> S.ELet (vr,ty, exp tenv' rhs) (exp tenv bod)
         where tenv' = M.insert vr ty tenv
       S.EPrimApp ty p args -> S.EPrimApp ty p (L.map (exp tenv) args)
       S.ECond e1 e2 e3 -> S.ECond (exp tenv e1) (exp tenv e2) (exp tenv e3)
       S.EIndexScalar ae ex -> S.EIndexScalar (aexp tenv ae) (exp tenv ex)
       S.EShapeSize ex -> S.EShapeSize (exp  tenv ex)
       S.EShape     ae -> S.EShape     (aexp tenv ae)

       S.EConst c  -> S.EConst c 
       S.ETuple ls -> S.ETuple (L.map (exp tenv) ls)
       S.ETupProjectFromRight ind ex -> S.ETupProjectFromRight ind (exp tenv ex)
       
       S.EIndex els -> S.EIndex (L.map (exp tenv) els)
       S.EIndexConsDynamic e1 e2 -> S.EIndexConsDynamic (exp tenv e1) (exp tenv e2)
       S.EIndexHeadDynamic ex -> S.EIndexHeadDynamic (exp tenv ex)
       S.EIndexTailDynamic ex -> S.EIndexTailDynamic (exp tenv ex)
