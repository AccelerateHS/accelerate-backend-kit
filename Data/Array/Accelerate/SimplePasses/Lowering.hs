{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}


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

--------------------------------------------------------------------------------
-- Compiler pass to lift Lets
--------------------------------------------------------------------------------

-- | This pass lifts all Let bindings to the outside.  
-- 
--   @Apply@ also gets converted to @Let@ in this pass.
-- 
--   The resulting program will have a spine of Lets (with Let-free
--   RHS's) followed by a Let-free body.
liftLets :: T.AExp -> T.AExp
liftLets x = 
     if L.null binds then loop binds else
     trace ("[dbg] Lifted out "++show (length binds)++" Lets ...") $ loop binds
  where (binds, bod) = gatherLets x
        loop [] = bod
        loop (hd:tl) = T.Let hd $ loop tl

gatherLets :: T.AExp -> ([(S.Var, S.Type, T.AExp)], T.AExp)
gatherLets prog = (reverse binds, prog')
 where 
   (prog',binds) = runState (loop prog) [] 
   addbind bnd = do ls <- get; put (bnd:ls)
   loop :: T.AExp -> State [(S.Var, S.Type, T.AExp)] T.AExp
   loop aex = 
     case aex of 
       T.Let (v,ty,rhs) bod -> 
          do rhs' <- loop rhs -- Important: Collect these bindings first.
             addbind (v,ty,rhs')
             loop bod
       T.Apply fn ae -> 
          do let T.ALam (v,ty) abod = fn 
             rhs' <- loop ae
             addbind (v,ty,rhs')
             loop abod
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       T.Vr vr               -> return aex
       T.Unit ex             -> return aex
       T.Use ty arr          -> return aex
       T.Generate aty ex fn  -> return aex
       T.ZipWith fn ae1 ae2  -> T.ZipWith fn <$> loop ae1 <*> loop ae2 
       T.Map     fn ae       -> T.Map     fn <$> loop ae
       T.TupleRefFromRight ind ae -> T.TupleRefFromRight ind <$> loop ae
       T.Cond ex ae1 ae2     -> T.Cond ex <$> loop ae1 <*> loop ae2 
       T.Replicate aty slice ex ae -> T.Replicate aty slice ex <$> loop ae
       T.Index     slc ae ex -> (\ ae' -> T.Index slc ae' ex) <$> loop ae
       T.Fold  fn einit ae         -> T.Fold  fn einit    <$> loop ae
       T.Fold1 fn       ae         -> T.Fold1 fn          <$> loop ae 
       T.FoldSeg fn einit ae aeseg -> T.FoldSeg fn einit  <$> loop ae <*> loop aeseg 
       T.Fold1Seg fn      ae aeseg -> T.Fold1Seg fn       <$> loop ae <*> loop aeseg 
       T.Scanl    fn einit ae      -> T.Scanl    fn einit <$> loop ae  
       T.Scanl'   fn einit ae      -> T.Scanl'   fn einit <$> loop ae  
       T.Scanl1   fn       ae      -> T.Scanl1   fn       <$> loop ae 
       T.Scanr    fn einit ae      -> T.Scanr    fn einit <$> loop ae 
       T.Scanr'   fn einit ae      -> T.Scanr'   fn einit <$> loop ae 
       T.Scanr1   fn       ae      -> T.Scanr1   fn       <$> loop ae
       T.Permute fn2 ae1 fn1 ae2 -> (\ a b -> T.Permute fn2 a fn1 ae2)
                                 <$> loop ae1 <*> loop ae2
       T.Backpermute ex lam ae -> T.Backpermute ex lam   <$> loop ae
       T.Reshape     ex     ae -> T.Reshape     ex       <$> loop ae
       T.Stencil   fn bndry ae -> T.Stencil     fn bndry <$> loop ae
       T.Stencil2  fn bnd1 ae1 bnd2 ae2 -> (\ a b -> T.Stencil2 fn bnd1 a bnd2 b) 
                                        <$> loop ae1 <*> loop ae2
       T.ArrayTuple aes -> T.ArrayTuple <$> mapM loop aes


--------------------------------------------------------------------------------
-- Compiler pass to remove Array tuples
--------------------------------------------------------------------------------

type SubNameMap = M.Map S.Var [S.Var]
-- | A binding EITHER for a scalar or array variable:
type Bindings a = [(S.Var, S.Type, a)]
type FlexBindings = Bindings (Either T.Exp S.AExp)

type CollectM = State (Int, Bindings T.Exp)

-- A temporary tree datatype.  This is used internally in `removeArrayTuple`.
data TempTree a = TT a a [TempTree a] -- Node of degree two or more 
                | TLeaf a

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
removeArrayTuple :: ([(S.Var, S.Type, T.AExp)], T.AExp) -> S.Prog
removeArrayTuple (binds, bod) = evalState main (0,[])
  where    
   main = do (newbinds,nameMap) <- doBinds [] M.empty binds
             newbod      <- dorhs nameMap bod
             newbinds2   <- dischargeNewScalarBinds
--             let finalbinds = mapBindings convertEither newbinds 
--                              ++ newbinds2
             let finalbinds = undefined
             return $ S.Letrec finalbinds
--                               (L.map convertAExps $ deepDeTuple nameMap newbod)
--                               (deepDeTuple nameMap newbod)
--                               (deTuple nameMap newbod)
                               (flattenTT newbod)
                               (S.TTuple [])
 
   -- Called on already processed expressions:
--    deepDeTuple :: SubNameMap -> T.AExp -> [T.AExp]
--    deepDeTuple eenv ae = 
--      case ae of      
--        T.ArrayTuple ls   -> concatMap (deepDeTuple eenv) ls
--        oth -> [oth]

   flattenTT :: TempTree S.AExp -> [S.AExp]
   flattenTT  ae = undefined
--      case ae of      
--        T.ArrayTuple ls   -> concatMap (deepDeTuple eenv) ls
--        oth -> [oth]

    
   mapBindings fn [] = []
   mapBindings fn ((v,t,x):tl) = (v,t,fn x) : mapBindings fn tl
   convertEither (Left  ex) = Left  $ convertExps  ex
   convertEither (Right ae) = Right $ convertAExps ae

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
           T.Vr v2          -> isTupledVar v2
           T.ArrayTuple ls  -> True
           T.Cond _ ae1 ae2 -> loop ae1 `strictAnd` loop ae2
           _                -> False
   
   isTupled (T.ArrayTuple _) = True
   isTupled (T.Vr vr)        = isTupledVar vr
   isTupled  _               = False

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
   doBinds :: FlexBindings -> SubNameMap -> [(S.Var, S.Type, T.AExp)] 
           -> CollectM (FlexBindings,SubNameMap)
   doBinds acc macc [] = return (reverse acc, macc)
   doBinds acc macc ((vr,ty,rhs) :remaining) = do 
     rhs' <- dorhs macc rhs     
     rhsScalars <- dischargeNewScalarBinds 
     
--      let (macc',thisbnd) = 
--            case rhs' of
--             TLeaf ae -> (macc, [(vr,ty,Right rhs')])
--             TT one two rest -> error "doBInds- FINISH THIS"
--          acc'  = error "FINISHIT" -- rhsScalars ++ thisbnd ++ acc
         
     let (macc',thisbnd) = 
           case L.map Right $ flattenTT rhs' of
             [ae] -> (macc, [(vr,ty,ae)]) -- No fresh names.
             unpacked -> 
               let subnames  = freshNames vr (length unpacked)
                   flattened = zip3 subnames (deTupleTy ty) unpacked 
               in (M.insert vr subnames macc, flattened)
--      let -- unpacked  = deTuple macc $ flattenTT rhs'
--          unpacked  = L.map Right $ flattenTT rhs'
--          subnames  = freshNames vr (length unpacked)
--          flattened = zip3 subnames (deTupleTy ty) unpacked 
--          (macc',thisbnd) = 
--            if length subnames > 1 
--            then (M.insert vr subnames macc, flattened)
--            else (macc, [(vr,ty,Right rhs')])

--      let unpacked  = L.map Right$ deTuple macc rhs'
--          subnames  = freshNames vr (length unpacked)
--          flattened = zip3 subnames (deTupleTy ty) unpacked 
--          (macc',thisbnd) = 
--            if length subnames > 1 
--            then (M.insert vr subnames macc, flattened)
--            else (macc, [(vr,ty,Right rhs')])
     
     let acc'  = rhsScalars ++ thisbnd ++ acc
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
       T.ArrayTuple ls   -> ls
       T.Vr vr -> 
         case M.lookup vr eenv of 
           Just newNames -> L.map T.Vr newNames
           Nothing -> error$"removeArrayTuple: variable not bound at this point: "++show vr
       oth -> [oth]
       
   -- Types are stored in reverse order from natural Accelerate textual order:
   -- deTupleTy (S.TTuple ls) = concatMap deTupleTy (reverse ls)
   deTupleTy (S.TTuple ls) = reverse ls
   deTupleTy oth           = [oth]

   -- For array expressions that we know are not tuples:
   arrayonly eenv aex = 
     case aex of 
       T.ArrayTuple ls -> error$"removeArrayTuple: encountered ArrayTuple that was not on the RHS of a Let:\n"++show(doc aex)
       T.Cond ex ae1 ae2 -> T.Cond ex <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
--       oth -> dorhs eenv oth
   
   -- Process the right hand side of a binding, breakup up Conds and
   -- rewriting variable references to their new detupled targets.
   dorhs :: M.Map S.Var [S.Var] -> T.AExp -> CollectM (TempTree S.AExp)
   dorhs = undefined
#if 0   
   -- The eenv here maps old names onto a list of new "subnames" for
   -- tuple components.  
   dorhs eenv aex = 
     case aex of 
       
       -- Variable references to tuples need to be deconstructed.
       -- The original variable will disappear.
       T.Vr vr -> case M.lookup vr eenv of  
                    Just names -> return $ mkArrayTuple (L.map S.Vr names)
                    Nothing    -> return aex
       
       -- Have to consider flattening of nested array tuples here:
       -- T.ArrayTuple ls -> concatMap (dorhs eenv) $ ls
       T.ArrayTuple ls -> S.ArrayTuple <$> mapM (dorhs eenv) ls 
       
       -- T.TupleRefFromRight ind ae | not (isTupled ae) -> 
       --   error "removeArrayTuple: TupleRefFromRight with unexpected input: "++show ae
       T.TupleRefFromRight ind ae -> do
         rhs' <- dorhs eenv ae
         return $ reverse (deTuple eenv rhs') !! ind
       
       -- Conditionals with tuples underneath need to be broken up:
       T.Cond ex ae1 ae2 | isTupled aex ->         
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
       
       T.Cond ex ae1 ae2 -> S.Cond ex <$> dorhs eenv ae1 <*> dorhs eenv ae2
       
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       T.Unit ex                   -> S.Unit (cE ex)
       T.Use ty arr                -> S.Use ty arr
       T.Generate aty ex fn        -> S.Generate aty (cE ex) fn
       T.ZipWith fn ae1 ae2        -> S.ZipWith fn <$> arrayonly eenv ae1 <*> arrayonly eenv ae2 
       T.Map     fn ae             -> S.Map     fn <$> arrayonly eenv ae
       T.TupleRefFromRight ind ae  -> S.TupleRefFromRight ind <$> arrayonly eenv ae
       T.Cond ex ae1 ae2           -> S.Cond (cE ex) <$> arrayonly eenv ae1 <*> arrayonly eenv ae2 
       T.Replicate aty slice ex ae -> S.Replicate aty slice (cE ex) <$> arrayonly eenv ae
       T.Index     slc ae    ex    -> (\ ae' -> S.Index slc ae' (cE ex)) <$> arrayonly eenv ae
       T.Fold  fn einit ae         -> S.Fold  fn einit    <$> arrayonly eenv ae
       T.Fold1 fn       ae         -> S.Fold1 fn          <$> arrayonly eenv ae 
       T.FoldSeg fn einit ae aeseg -> S.FoldSeg fn einit  <$> arrayonly eenv ae <*> arrayonly eenv aeseg 
       T.Fold1Seg fn      ae aeseg -> S.Fold1Seg fn       <$> arrayonly eenv ae <*> arrayonly eenv aeseg 
       T.Scanl    fn einit ae      -> S.Scanl    fn einit <$> arrayonly eenv ae  
       T.Scanl'   fn einit ae      -> S.Scanl'   fn einit <$> arrayonly eenv ae  
       T.Scanl1   fn       ae      -> S.Scanl1   fn       <$> arrayonly eenv ae 
       T.Scanr    fn einit ae      -> S.Scanr    fn einit <$> arrayonly eenv ae 
       T.Scanr'   fn einit ae      -> S.Scanr'   fn einit <$> arrayonly eenv ae 
       T.Scanr1   fn       ae      -> S.Scanr1   fn       <$> arrayonly eenv ae
       T.Permute fn2 ae1 fn1 ae2   -> (\ a b -> S.Permute fn2 a fn1 ae2)
                                   <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
       T.Backpermute ex lam ae     -> S.Backpermute (cE ex) lam   <$> arrayonly eenv ae
       T.Reshape     ex     ae     -> S.Reshape     (cE ex)       <$> arrayonly eenv ae
       T.Stencil   fn bndry ae     -> S.Stencil     fn bndry <$> arrayonly eenv ae
       T.Stencil2  fn bnd1 ae1 bnd2 ae2 -> (\ a b -> S.Stencil2 fn bnd1 a bnd2 b) 
                                        <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
#endif
     
cE = convertExps    

mkArrayTuple [one] = one
mkArrayTuple ls    = T.ArrayTuple ls

--------------------------------------------------------------------------------
-- Compiler pass to remove dynamic cons/head/tail on indices.
--------------------------------------------------------------------------------

-- UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED 

-- | This removes dynamic cons/head/tail on indices.  Indices are
--   plain tuples after this pass.
staticTuples :: T.AExp -> T.AExp
staticTuples ae = aexp M.empty ae
 where
--   aexp :: M.Map Var Int -> AExp -> [Builder]
   
   -- Trace the spine of lets.  We allow array tuples only at the very end:
   prog tenv aex = 
     case aex of 
       -- Lift out Let's as we encounter them:
       T.Let (v1,t1, T.Let (v2,t2,rhs) bod1) bod2 -> 
         prog tenv $ T.Let (v2,t2,rhs) $
                     T.Let (v1,t1,bod1) bod2


--       T.Let (vr,ty,rhs) bod -> T.Let (vr,ty,aexp tenv' rhs) (tail tenv bod)
--          where tenv' = M.insert vr ty tenv
       oth -> aexp tenv oth

   aexp tenv aex = 
     case aex of 
       
       -- Here we convert Apply to Let:
       T.Apply fn ae -> 
         T.Let (v,ty, aexp tenv' abod) (aexp tenv ae)
         where tenv' = M.insert v ty tenv         
               T.ALam (v,ty) abod = fn 
       
       -- TODO: Can we get rid of array tupling entirely?
       T.ArrayTuple aes -> T.ArrayTuple $ L.map (aexp tenv) aes       

       -- T.Let (vr,ty, T.ArrayTuple rhss) bod -> error "T.Let FINISHME"
         -- T.Let (vr,ty,loop rhs) (loop bod)
         -- where loop = aexp (M.insert vr ty tenv)

       -- The rest is BOILERPLATE; could scrap if we so chose:
       -------------------------------------------------------
       T.Vr vr -> T.Vr vr
       T.Let (vr,ty,rhs) bod -> T.Let (vr,ty,aexp tenv' rhs) (aexp tenv bod)
          where tenv' = M.insert vr ty tenv
       T.Unit ex -> T.Unit (exp tenv ex)
            
       T.Generate aty ex fn -> T.Generate aty (exp tenv ex) (lam1 tenv fn)
       T.ZipWith fn ae1 ae2 -> T.ZipWith (lam2 tenv fn) (aexp tenv ae1) (aexp tenv ae2)
       T.Map     fn ae      -> T.Map (lam1 tenv fn) (aexp tenv ae)

       T.TupleRefFromRight ind ae -> T.TupleRefFromRight ind (aexp tenv ae)

       T.Cond ex ae1 ae2 -> T.Cond (exp tenv ex) (aexp tenv ae1) (aexp tenv ae2)
       T.Use ty arr -> T.Use ty arr
 
       T.Replicate aty slice ex ae -> T.Replicate aty slice (exp tenv ex) (aexp tenv ae)
       T.Index     slc ae ex -> T.Index slc (aexp tenv ae) (exp tenv ex)
              
       T.Fold  fn einit ae         -> T.Fold  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Fold1 fn       ae         -> T.Fold1 (lam2 tenv fn) (aexp tenv ae)
       T.FoldSeg fn einit ae aeseg -> T.FoldSeg  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae) (aexp tenv aeseg)
       T.Fold1Seg fn      ae aeseg -> T.Fold1Seg (lam2 tenv fn) (aexp tenv ae) (aexp tenv aeseg)
       T.Scanl    fn einit ae      -> T.Scanl  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanl'   fn einit ae      -> T.Scanl' (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanl1   fn       ae      -> T.Scanl1 (lam2 tenv fn) (aexp tenv ae)
       T.Scanr    fn einit ae      -> T.Scanr  (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanr'   fn einit ae      -> T.Scanr' (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanr1   fn       ae      -> T.Scanr1 (lam2 tenv fn) (aexp tenv ae)

       T.Permute fn2 ae1 fn1 ae2 -> 
         T.Permute (lam2 tenv fn2) (aexp tenv ae1) 
                   (lam1 tenv fn1) (aexp tenv ae2)

       T.Backpermute ex lam ae -> T.Backpermute (exp tenv ex) (lam1 tenv lam) (aexp tenv ae)
       T.Reshape     ex     ae -> T.Reshape     (exp tenv ex)                 (aexp tenv ae)
       T.Stencil   fn bndry ae -> T.Stencil     (lam1 tenv fn) bndry          (aexp tenv ae)
       T.Stencil2  fn bnd1 ae1 bnd2 ae2 ->  T.Stencil2 (lam2 tenv fn) bnd1 (aexp tenv ae1)
                                                                      bnd2 (aexp tenv ae2)
   -- Handle arity 1 lambdas:
   lam1 tenv (T.Lam1 (v,ty) bod) = T.Lam1 (v,ty) (exp tenv' bod)
     where tenv' = M.insert v ty tenv
   -- Handle arity 2 lambdas:
   lam2 tenv (T.Lam2 (v1,ty1) (v2,ty2) bod) = T.Lam2 (v1,ty1) (v2,ty2) (exp tenv' bod)
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
