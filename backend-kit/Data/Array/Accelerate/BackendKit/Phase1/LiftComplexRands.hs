{-# LANGUAGE TupleSections #-}

--------------------------------------------------------------------------------
-- | Compiler pass to lift complex operands into let bindings
--------------------------------------------------------------------------------

module Data.Array.Accelerate.BackendKit.Phase1.LiftComplexRands
       ( liftComplexRands )
       where

import Control.Applicative        ((<$>),(<*>))
import Control.Monad.State.Strict (State, evalState, runState, get, put, modify)
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc  as S
import Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone as T
import Prelude                                    hiding (sum, exp)

-- Shorthands:
type TAExp = T.AExp S.Type
type Binding  a = (S.Var, S.Type, a)
type Bindings a = [Binding a]

isAVar :: T.AExp t -> Bool
isAVar (T.Vr _ _)  = True
isAVar _           = False

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
liftComplexRands orig_aex =
    -- By starting off with 'flat' we ALSO lift the body of the whole program
    -- evalState (flat aex) (0,[])
    evalState (discharge (flat orig_aex)) 0
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
        -- FIXME: use the genUnique library routine:
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
       T.ETupProject ind len ex      -> T.ETupProject ind len <$> exp ex
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

