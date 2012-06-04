{-# LANGUAGE CPP #-}
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
type Bindings a = [(S.Var, S.Type, a)]
type FlexBindings = Bindings (Either T.Exp S.AExp)

type CollectM = State (Int, Bindings T.Exp)

-- A temporary tree datatype.  This is used internally in `removeArrayTuple`.
data TempTree a = TT (TempTree a) (TempTree a) [TempTree a] -- Node of degree two or more 
                | TLeaf a
  deriving Show                 

listToTT [] = error "listToTT: We are only representing non-empty tuples of arrays here... looks like that's not good enough"
listToTT [x] = x 
listToTT (x:y:tl) = TT x y tl

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
             -- LIFT the body out.  This should be part of a different
             -- pass.  But because we don't have a
             -- scrap-your-boilerplate right now, that's too
             -- inconvenient:
             -- -- TODO -- LIFT BODY OUT
             
             let finalbinds = mapBindings convertLeft (newbinds ++ newbinds2)
             return $ S.Letrec finalbinds
                               (flattenTT newbod)
                               (S.TTuple [])
 
   -- Called on already processed expressions:
   flattenTT :: TempTree S.AExp -> [S.AExp]
   flattenTT x = 
     case x of      
       TLeaf e   -> [e]
       TT a b ls -> flattenTT a ++ flattenTT b ++
                    concatMap flattenTT ls
    
   mapBindings fn [] = []
   mapBindings fn ((v,t,x):tl) = (v,t,fn x) : mapBindings fn tl

   convertLeft (Left  ex)  = Left  $ convertExps  ex
   convertLeft (Right ae) = Right ae

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
           T.Vr _ v2          -> isTupledVar v2
           T.ArrayTuple _ ls  -> True
           T.Cond _ _ ae1 ae2 -> loop ae1 `strictAnd` loop ae2
           _                  -> False
   
   isTupled (T.ArrayTuple _ _) = True
   isTupled (T.Vr _ vr)        = isTupledVar vr
   isTupled  _                 = False

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
     let acc'  = rhsScalars ++ thisbnd ++ acc
     doBinds acc' macc' remaining

   freshNames vr len = L.map (S.var . ((show vr ++"_")++) . show) [1..len]

   -- Types are stored in reverse order from natural Accelerate textual order:
   -- deTupleTy (S.TTuple ls) = concatMap deTupleTy (reverse ls)
   deTupleTy (S.TTuple ls) = reverse ls
   deTupleTy oth           = [oth]

   -- For array expressions that we know are not tuples:
   arrayonly :: SubNameMap -> TAExp -> CollectM S.AExp
   arrayonly eenv aex = 
     case aex of 
       T.ArrayTuple _ ls -> error$"removeArrayTuple: encountered ArrayTuple that was not on the RHS of a Let:\n"++show(doc aex)
       T.Cond _ ex ae1 ae2 -> S.Cond (cE ex) <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
       oth -> fromLeaf <$> dorhs eenv oth
   
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
       T.Cond ty ex ae1 ae2 | isTupled aex ->         
         -- Breaking up the conditional requires possibly let-binding the scalar expression:
         do 
            ae1' <- dorhs eenv ae1
            ae2' <- dorhs eenv ae2
            (cntr,bnds) <- get
            let triv = isTrivial ex  
            unless triv $ put (cntr+1, bnds)
            let fresh = S.var $ "cnd_" ++ show cntr
                ex' = if triv then ex' else S.EVr fresh
                ls1 = flattenTT ae1' -- These must be fully flattened if there are nested tuples.
                ls2 = flattenTT ae2'
                result = listOfLeaves $ L.map (uncurry $ S.Cond ex') (zip ls1 ls2)
            -- Here we add the new binding, if needed:
            let fakeType = trace "WARNING - REPLACE THIS WITH A REAL TYPE" (S.TTuple [])
            unless triv $ modify (\ (c,ls) -> (c, (fresh,fakeType,ex):ls))
            return result          

       T.Cond ty ex ae1 ae2 -> (\ a b -> TLeaf$ S.Cond (cE ex) (fromLeaf a) (fromLeaf b))
                            <$> dorhs eenv ae1 <*> dorhs eenv ae2
       
       -- The rest is BOILERPLATE:      
       ----------------------------------------      
       T.Unit ty ex                   -> return$ TLeaf$ S.Unit (cE ex)
       T.Use ty arr                -> return$ TLeaf$ S.Use ty arr
       T.Generate aty ex fn        -> return$ TLeaf$ S.Generate aty (cE ex) (cF fn)
       T.ZipWith ty fn ae1 ae2        -> lf$ S.ZipWith (cF2 fn) <$> arrayonly eenv ae1 <*> arrayonly eenv ae2 
       T.Map     ty fn ae             -> lf$ S.Map     (cF fn) <$> arrayonly eenv ae
       T.Replicate aty slice ex ae -> lf$ S.Replicate aty slice (cE ex) <$> arrayonly eenv ae
       T.Index     _ slc ae    ex    -> lf$ (\ ae' -> S.Index slc ae' (cE ex)) <$> arrayonly eenv ae
       T.Fold  _ fn einit ae         -> lf$ S.Fold  (cF2 fn) (cE einit)    <$> arrayonly eenv ae
       T.Fold1 _ fn       ae         -> lf$ S.Fold1 (cF2 fn)               <$> arrayonly eenv ae 
       T.FoldSeg _ fn einit ae aeseg -> lf$ S.FoldSeg (cF2 fn) (cE einit)  <$> arrayonly eenv ae <*> arrayonly eenv aeseg 
       T.Fold1Seg _ fn      ae aeseg -> lf$ S.Fold1Seg (cF2 fn)            <$> arrayonly eenv ae <*> arrayonly eenv aeseg 
       T.Scanl    _ fn einit ae      -> lf$ S.Scanl    (cF2 fn) (cE einit) <$> arrayonly eenv ae  
       T.Scanl'   _ fn einit ae      -> lf$ S.Scanl'   (cF2 fn) (cE einit) <$> arrayonly eenv ae  
       T.Scanl1   _ fn       ae      -> lf$ S.Scanl1   (cF2 fn)            <$> arrayonly eenv ae 
       T.Scanr    _ fn einit ae      -> lf$ S.Scanr    (cF2 fn) (cE einit) <$> arrayonly eenv ae 
       T.Scanr'   _ fn einit ae      -> lf$ S.Scanr'   (cF2 fn) (cE einit) <$> arrayonly eenv ae 
       T.Scanr1   _ fn       ae      -> lf$ S.Scanr1   (cF2 fn)            <$> arrayonly eenv ae
       T.Permute _ fn2 ae1 fn1 ae2   -> lf$ (\ a b -> S.Permute (cF2 fn2) a (cF fn1) b)
                                   <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
       T.Backpermute _ ex fn  ae     -> lf$ S.Backpermute (cE ex) (cF fn) <$> arrayonly eenv ae
       T.Reshape     _ ex     ae     -> lf$ S.Reshape     (cE ex)         <$> arrayonly eenv ae
       T.Stencil   _ fn bndry ae     -> lf$ S.Stencil     (cF fn) bndry   <$> arrayonly eenv ae
       T.Stencil2  _ fn bnd1 ae1 bnd2 ae2 -> lf$ (\ a b -> S.Stencil2 (cF2 fn) bnd1 a bnd2 b)
                                        <$> arrayonly eenv ae1 <*> arrayonly eenv ae2
       T.Let _ _ _   -> error$ "removeArrayTuple: not expecting Let; should have been removed."
       T.Apply _ _ _ -> error$ "removeArrayTuple: not expecting Apply; should have been removed."
     


lf x = TLeaf <$> x
cE = convertExps    
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
    -- By starting off with 'flat' we lift the body ALSO:
    evalState (flat aex) 0
  where  
   isVar :: TAExp -> Bool
   isVar aex = 
     case aex of 
       T.Vr _ _ -> True
       _        -> False
   flat :: TAExp -> State Int TAExp 
   flat aex | isVar aex = return aex
   flat (T.Let rt (v,ty,rhs) bod) = do
     rhs' <- loop rhs
     bod' <- flat bod
     return$ T.Let rt (v,ty,rhs') bod'
   flat (T.Apply rt fn ae) = do -- Let's in disguise.
     let S.Lam1 (v,ty) abod = fn 
     rand' <- loop ae
     abod' <- flat abod
     return$ T.Apply rt (S.Lam1 (v,ty) abod') rand'
   -- Otherwise we lift it into a Let:
   flat aex = 
     do tmp <- tmpVar
        let ty = getAnnot aex
        rhs' <- loop aex
        return$ T.Let ty (tmp,ty, rhs') (T.Vr ty tmp)
   
   tmpVar :: State Int S.Var
   tmpVar = 
     do cnt <- get 
        put (cnt+1)
        return$ S.var $ "tmp_"++show cnt
   loop :: TAExp -> State Int TAExp -- Keeps a counter.
   loop aex = 
     case aex of 
       T.Vr _ _              -> return aex
       T.Unit _ _            -> return aex
       T.Use _ _             -> return aex
       T.Generate _ _ _      -> return aex
       T.Let rt (v,ty,rhs) bod -> 
          do rhs' <- loop rhs 
             bod' <- loop bod
             return$ T.Let rt (v,ty,rhs') bod'
       T.Apply rt fn ae -> 
          do let S.Lam1 (v,ty) abod = fn 
             rand' <- loop ae
             abod' <- loop abod
             return$ T.Apply rt (S.Lam1 (v,ty) abod') rand'
       T.ZipWith a fn ae1 ae2  -> T.ZipWith a fn <$> flat ae1 <*> flat ae2 
       T.Map     a fn ae       -> T.Map     a fn <$> flat ae
       T.TupleRefFromRight a ind ae -> T.TupleRefFromRight a ind <$> flat ae
       T.Cond a ex ae1 ae2     -> T.Cond a ex <$> flat ae1 <*> flat ae2 
       T.Replicate aty slice ex ae -> T.Replicate aty slice ex <$> flat ae
       T.Index     a slc ae ex -> (\ ae' -> T.Index a slc ae' ex) <$> flat ae
       T.Fold  a fn einit ae         -> T.Fold  a fn einit    <$> flat ae
       T.Fold1 a fn       ae         -> T.Fold1 a fn          <$> flat ae 
       T.FoldSeg a fn einit ae aeseg -> T.FoldSeg a fn einit  <$> flat ae <*> flat aeseg 
       T.Fold1Seg a fn      ae aeseg -> T.Fold1Seg a fn       <$> flat ae <*> flat aeseg 
       T.Scanl    a fn einit ae      -> T.Scanl    a fn einit <$> flat ae  
       T.Scanl'   a fn einit ae      -> T.Scanl'   a fn einit <$> flat ae  
       T.Scanl1   a fn       ae      -> T.Scanl1   a fn       <$> flat ae 
       T.Scanr    a fn einit ae      -> T.Scanr    a fn einit <$> flat ae 
       T.Scanr'   a fn einit ae      -> T.Scanr'   a fn einit <$> flat ae 
       T.Scanr1   a fn       ae      -> T.Scanr1   a fn       <$> flat ae
       T.Permute a fn2 ae1 fn1 ae2 -> (\ x y -> T.Permute a fn2 x fn1 y)
                                  <$> flat ae1 <*> flat ae2
       T.Backpermute a ex lam ae -> T.Backpermute a ex lam   <$> flat ae
       T.Reshape     a ex     ae -> T.Reshape     a ex       <$> flat ae
       T.Stencil   a fn bndry ae -> T.Stencil     a fn bndry <$> flat ae
       T.Stencil2  a fn bnd1 ae1 bnd2 ae2 -> (\ x y -> T.Stencil2 a fn bnd1 x bnd2 y) 
                                        <$> flat ae1 <*> flat ae2
       T.ArrayTuple a aes -> T.ArrayTuple a <$> mapM flat aes
