{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This pass does the final conversion to CLike IR format.  Unfortunately it
--   does more work than that along the way.  In particular it finishes the rest of
--   the unzipping process, and incidentally does copy-prop.

module Data.Array.Accelerate.BackendKit.Phase2.ToCLike (convertToCLike) where

import qualified Data.Map   as M
import           Data.List  as L
import           Data.Maybe (fromJust)
import           Control.Monad.Writer
import           Control.Applicative   ((<$>),(<*>))
import           Control.Monad.State.Strict
import           Text.PrettyPrint.GenericPretty (Out(doc))

import qualified Data.Array.Accelerate.BackendKit.IRs.CLike as LL
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.Metadata
                   (OpInputs(..),SubBinds(..), Stride(..), ArraySizeEstimate(..))
import           Data.Array.Accelerate.BackendKit.Utils.Helpers
                   (genUnique, genUniqueWith, GensymM, isTupleTy, (#), fragileZip)

import           Data.Array.Accelerate.BackendKit.Phase2.UnzipETups (flattenEither)

import Debug.Trace (trace)
import Text.Printf

----------------------------------------------------------------------------------------------------

-- | Callback functions for writing results (continuations):
type Cont = [LL.Exp] -> [LL.Stmt]

-- | Unfortunately, this pass needs to do a bit of left-over tuple unzipping
--   too.  For this it carries an environment that maps tupled variables to
--   their detupled subcomponents.  (Note that the same mechanism can also be
--   reused simple to alpha rename vars; i.e. a singleton [Var] list.)
--
--   The Env tracks size as well (for array binds only).  Note that TOP LEVEL
--   bindings have ALREADY been split, so they will appear in this environment in
--   their detupled form.  The [Var] component will only be non-singleton for
--   non-top-level scalar bindings that are being detupled *by this pass*.
type Env = M.Map Var (Type, [Var], Maybe TrivialExp)

-- | We have a hefty pile of metadata at this point.  Fortunately we get to discharge
-- it during this pass.
type FullMeta = (OpInputs,(SubBinds,(Maybe (Stride Exp), ArraySizeEstimate)))
----------------------------------------------------------------------------------------------------

-- | This pass takes a SimpleAST IR which already follows a number of
--   conventions that make it directly convertable to the lower level
--   IR, and it does the final conversion.
convertToCLike :: Prog FullMeta -> LL.LLProg ()
convertToCLike Prog{progBinds,progResults,progType,uniqueCounter,typeEnv} =
  let WithShapesUnzipped pR = progResults in
  LL.LLProg
  {
    LL.progBinds    = map (fmap (const ())) binds,
--    LL.progResults  = map (copyProp finalEnv) progResults,
    LL.progResults  = pR,
    LL.progType     = progType,
    LL.uniqueCounter= newCounter,
    LL.sizeEnv      = sizeEnv
  }
  where
    m = mapM (doBind initEnv) progBinds
    -- ((finalEnv,binds),newCounter) = runState m uniqueCounter
    (binds,newCounter) = runState m uniqueCounter

    -- Bindings for (detupled) scalar and array top-level variables:
    initEnv :: Env
    initEnv = M.fromList $
              L.map (\(v,sz) -> (v,(typeEnv#v, [v], sz))) $
              -- All top-level (detupled) bindings, throwing out any tupled ones:
              L.concatMap (\(ProgBind _ _ (_,(SubBinds vrs sz,_)) _) -> map (,sz) vrs)
                          progBinds

    -- Collect the size environment for the detupled bindings (easy):
    sizeEnv :: M.Map Var (Type, TrivialExp)
    sizeEnv = L.foldl red M.empty progBinds
    -- FIXME: Scanl' breaks the assumption about TArray for array ops:
    red acc (ProgBind _ (TArray _ elt) (_,(SubBinds vrs szE,_)) _) =
      let Just triv = szE in
      M.union (M.fromList [ (vr,(ty,triv))
                          | (vr,ty) <- fragileZip vrs (gentlyFlatten elt) ])
              acc
    red acc _ = acc

gentlyFlatten :: Type -> [Type]
gentlyFlatten (TTuple [])  = [TTuple []]
gentlyFlatten (TTuple ls)  = concatMap gentlyFlatten ls
gentlyFlatten         ty  = [ty]


doBlock :: Env -> Exp -> GensymM LL.ScalarBlock
doBlock env ex = do
  -- Here we need to recover the type of the result to introduce temporary variables:
  let ty = recoverExpType (unliftEnv env) ex
  (binds,cont)   <- makeResultWriterCont ty
  (stmts,binds2) <- runWriterT$ doStmts cont env ex
  return$ LL.ScalarBlock (binds++binds2) (L.map fst binds) stmts

-- | Create temporary bindings and the callback/continuation that writes them.
makeResultWriterCont :: Type -> GensymM ([(Var,Type)], Cont)
makeResultWriterCont ty = do
  tmps <- sequence$ replicate (S.countTyScalars ty) genUnique
  let binds = zip tmps (S.flattenTy ty)
      cont results =
        L.zipWith (\ tmp result -> LL.SSet tmp (result))
          tmps results
  return (binds,cont)


--
hackAssign :: [Var] -> Cont -> [LL.Stmt]
hackAssign vs f = f (L.map LL.EVr vs)

-- | This takes a continuation for where to write the results.
--
-- Returns:
--  (1) list of vars where the final return values reside
--  (2) a list of statements encoding the computation
doStmts :: Cont -> Env -> Exp ->
           WriterT [(Var,Type)] GensymM [LL.Stmt]
doStmts k env ex =
  case ex of
    ELet (vr,ty, bnd@ECond{}) bod  -> do
      -- Introduce a new temporaries and a continuation for the non-tail conditional:
      (binds,k') <- lift $ makeResultWriterCont ty
      mytell binds

      let env'          = M.insert vr (ty,subcomps,Nothing) env
          subcomps      = L.map fst binds

      bnd' <- doStmts k' env  bnd
      bod' <- doStmts k  env' bod
      return $ bnd' ++ bod'

    -- In the case of a while in the RHS of a Let,
    -- ty can be a tuple type at this point.
    ELet (vr, ty, bnd@EWhile{}) bod -> do
      -- Assumption: ty == recoverExpType bod
--      let  (Lam1 (v1,t1) bod1) = a
--           (Lam1 (v2,t2) bod2) = b

      -- Introduce new temp vars For the result of the 'While' loop
      (binds, k') <- lift $ makeResultWriterCont ty
      mytell binds
      let env'          = M.insert vr (ty,subcomps,Nothing) env
          subcomps      = L.map fst binds

      -- trace (printf "doStmts: ELet/EWhile binds = %s\n" (show binds)) $ return ()
      -- trace (printf "doStmts: ELet/EWhile processing loop:\n  %s\n" (show bnd)) $ return ()

      bnd' <- doStmts k' env  bnd
      bod' <- doStmts k  env' bod
      return $ bnd' ++ bod'

    ELet (vr,ty,rhs) bod ->
      do
         if (isTupleTy ty)
         then error $"ToCLike.hs: internal error, tupled type still remaining in bindings  ***Let case*** : "++show ty ++ " RHS=" ++ show rhs
         else mytell [(vr,ty)]
         let env' = M.insert vr (ty,[vr],Nothing) env
         rest <- doStmts k env' bod
         return (LL.SSet vr (doE env rhs) : rest)

    ECond a b c -> fmap sing $
      LL.SCond (doE env a) <$> doStmts k env b <*> doStmts k env c

    -- Handle While here
    -- Previously this was in doE (so used the fallthrough below)
    EWhile p f x -> do
      -- The function bodies
      (bnd1, p') <- doLam1 env p      
      (bnd2, f') <- doLam1 env f

      -- The initial value needs to be wrapped in a standalone scalar block
      (bnd3, k')   <- lift $ makeResultWriterCont (recoverExpType (unliftEnv env) x)
      (x',bnd3')   <- lift $ runWriterT (doStmts k' env x)
      let x''       = LL.ScalarBlock (bnd3++bnd3') (L.map fst bnd3) x'

      -- Need to declare the bindings for the predicate function and body of the
      -- loop outside of the while block.
      mytell (bnd1 ++ bnd2 ++ bnd3)
      --mytell bnd3 
                      
      -- Just below the loop body, assign the final loop values to some fresh
      -- variables.
      return $ LL.SWhile ((fst . head) bnd1) p' f' x''
             : hackAssign (L.map fst bnd2) k

      
    -- An ETuple in tail position:
    ETuple ls -> return$ k$ L.map (doE env) ls

    -- Anything else had better be just an expression in the new IR:
    oth -> return$ k [doE env oth]
--  where
   
mytell ls =
    if any isTupleTy (map snd ls)
    then error$"ToCLike.hs: internal error, tupled type still remaining in bindings: "++show ls
    else tell ls

-- Turn a 'Lam1 Exp' into a 'Lam1 ScalarBlock' given an env. Each lambda needs
-- to be handled like this:
--
-- * recover the type of the scalar block body
-- * generate a new continuation
-- * recurse on the scalar block with the new continuation
-- * construct a LL.Lam with an LL.ScalarBlock
--
doLam1 :: Env -> S.Fun1 S.Exp -> WriterT [(Var, Type)]  GensymM ([(Var,Type)], LL.Fun LL.ScalarBlock)
doLam1 env (Lam1 (v,t) bod) =
  do let ft = S.flattenTy t
     vs <- lift $ genUniques v (length ft)
     let env' = M.insert v (t,vs,Nothing) env
         vt   = zip vs ft

     -- mytell vt

     let ty = recoverExpType (unliftEnv env') bod
     (binds,cont)   <- lift $ makeResultWriterCont ty
     (stmts,binds') <- lift $ runWriterT $ doStmts cont env' bod
     -- trace ("doLam1: " ++ show vt ++ "\n" ++ show binds ++ "\n" ++ show binds') 
     return (binds++binds', LL.Lam vt $ LL.ScalarBlock (binds ++ binds') (L.map fst binds) stmts)


doBind :: Env -> ProgBind FullMeta -> GensymM (LL.LLProgBind FullMeta)
doBind env (ProgBind _ ty decor@(OpInputs vis, (SubBinds vos _, (foldstride, _))) rhs) = do
  rhs' <- case rhs of
            Left  ex -> LL.ScalarCode <$> doBlock env ex
            Right ae -> doAE ae

  let outBinds = fragileZip vos (flattenEither ty)
  return (LL.LLProgBind outBinds decor rhs')

 where
   -- Uses 'vis' and 'foldstride' above:
   doAE :: AExp -> GensymM LL.TopLvlForm
   doAE ae =
     case ae of
       Vr v          -> error$ "ToCLike.hs: Array variable should have been eliminated by copy-prop: "++show v
       Cond a _ _    ->
         case vis of
           [[b'],[c']] -> return$ LL.Cond (doE env a) b' c'
           _           -> error$"ToCLike.hs: cannot yet handle array Cond with array-of-tuples in branches: "++show vis
       Use  arr      -> return$ LL.Use  arr
       Use' v dim ty -> return$ LL.Use' v dim ty

       Generate ex (Lam1 (vr,ty) bod) -> do
         -- Because arrays are 1D at this point, ex and vr are scalar.
         -- 'ex' should be of type TInt, and it should be trivial.
         let env' = M.insert vr (ty,[vr],error"SIZE") env
         LL.GenManifest <$>
           LL.Gen (doTriv ex)
             <$> (LL.Lam [(vr,ty)] <$> doBlock env' bod)

       -- TODO: Implement greedy fold/generate fusion RIGHT HERE:
       Fold  lam2 ex _     -> foldHelp (head vis) (doStride foldstride) lam2
                                       =<< (LL.Fold <$> doBlock env ex)
       FoldSeg lam2 ex _ _ -> do let [inVs,segVs] = vis
                                 initSB <- doBlock env ex
                                 foldHelp inVs (doStride foldstride) lam2
                                   (LL.FoldSeg initSB (LL.Manifest segVs))
       Fold1 lam2 _    -> foldHelp (head vis) LL.StrideAll lam2 LL.Fold1
       Fold1Seg {}     -> err
       Scanl lam2 ex _ -> foldHelp (head vis) LL.StrideAll lam2 =<< (LL.Scan LL.LeftScan  <$> doBlock env ex)
       Scanr lam2 ex _ -> foldHelp (head vis) LL.StrideAll lam2 =<< (LL.Scan LL.RightScan <$> doBlock env ex)
       -- NOTE: Scan1 doesn't have an InitialValue parameter!
       Scanl1 lam2 _   -> foldHelp (head vis) LL.StrideAll lam2 (LL.Scan1 LL.LeftScan)
       Scanr1 lam2 _   -> foldHelp (head vis) LL.StrideAll lam2 (LL.Scan1 LL.RightScan)
       Scanl' {}       -> err
       Scanr' {}       -> err
       Unit         {} -> err
       Replicate    {} -> err
       Reshape      {} -> err
       Permute      {} -> err
       Backpermute  {} -> err
       Index        {} -> err
       Map          {} -> err
       ZipWith      {} -> err
       Stencil      {} -> err
       Stencil2     {} -> err
     where
      err = error$"ToCLike.hs/doAE: this form should be desugared by now: "++show ae

   doStride (Just (StrideConst ex)) = LL.StrideConst$ doE env ex
   doStride (Just (StrideAll))      = LL.StrideAll

   foldHelp inVs' stride (Lam2 (v,t) (w,u) bod) variant = do
      let vtys = S.flattenTy t
          wtys = S.flattenTy u
      vs' <- genUniques v (length vtys)
      ws' <- genUniques w (length wtys)
      let env' = M.insert v (t,vs',Nothing) $
                 M.insert w (u,ws',Nothing) env
          args = zip vs' vtys ++ zip ws' wtys
      LL.GenReduce <$> (LL.Lam args <$> doBlock env' bod)
                   <*> return (LL.Manifest inVs')
                   <*> return variant
                   <*> return stride


doTriv :: Exp -> TrivialExp
doTriv (EVr v)       = TrivVarref v
doTriv (EConst (I n)) = TrivConst n
doTriv oth           = error$"Expected trivial expression, got "++show oth

-- Handle simple, non-spine expressions:
doE :: Env -> Exp -> LL.Exp
doE env ex =
  case ex of
    EVr vr           -> case M.lookup vr env of
--                         Just (_,_,Nothing)    -> LL.EVr vr
                         Just (_,[vr2],_) -> LL.EVr vr2
                         Just (_, ls , _) -> error$"ToCLike.hs/doE: uncaught raw reference to tuple-bound variable: "
                                                  ++show vr++" subcomponents "++show ls
                         Nothing -> error$"ToCLike.hs/doE: internal error, var not in env: "++show vr
    ETupProject ind 1 (EVr vr) ->
      case M.lookup vr env of
        Just (_,ls,_) -> LL.EVr $ (reverse ls) !! ind
          -- trace (printf "trying to project tuple index %d from variables %s\n" ind (show ls))
        oth -> error$"ToCLike.hs/doE: internal error, tuple project of field "++show ind++
                     " of var: "++show vr++", env binding: "++show oth

    ETupProject _ _ _ -> error"FINISHME -- ETupProject"

    EConst c         -> case c of
                          Tup _ -> error$"ToCLike.hs: should not have remaining tuple constants: "++show c
                          oth   -> LL.EConst c
    EPrimApp ty p ls -> LL.EPrimApp ty p $ L.map (doE env) ls
    ECond a b c      -> LL.ECond (doE env a) (doE env b) (doE env c)

    -- 'While' used to be here, but it can't be, because this function returns an LL.Exp,
    -- of which 'while' is not. There is an incomplete case error that pops up here,
    -- which is unfortunate; at some point in the code, doE is being called on a while,
    -- which is not correct.

    EIndexScalar v e -> LL.EIndexScalar v (doE env e) 0
    EIndex _     -> err
    EShapeSize _ -> err
    ELet _ _     -> err
    EShape _     -> err
    ETuple _     -> err
  where err = error$"ToCLike.hs/doE: this form should not occur in a non-spine expression: "++show ex


----------------------------------------------------------------------------------------------------
-- Little Helpers:

sing :: t -> [t]
sing x = [x]

-- Lift our extended environment down to a basic type env
unliftEnv :: M.Map Var (Type, a,b) -> M.Map Var Type
unliftEnv = M.map (\ (t,_,_) -> t)


----------------------------------------------------------------------------------------------------
-- Unit testing:

p1 :: Exp
p1 = ECond (EConst (B True))
--          (EVr$ var "x") (EVr$ var "y")
           (EConst (I 8)) (EConst (I 16))

t1 :: (LL.ScalarBlock, Int)
t1 = runState (doBlock M.empty p1) 1000

t2 :: (LL.ScalarBlock, Int)
t2 = (`runState` 1000) $
  doBlock M.empty $
    ECond (EConst (B False))
          (EConst (I 32)) p1


genUniques :: Var -> Int -> GensymM [Var]
genUniques v n =
  sequence$ map genUniqueWith (replicate n (show v))

-- | Introduce a temporary variable just for the purpose of lifting an Exp to a ScalarBlock.
exp2Blk :: Type -> LL.Exp -> GensymM LL.ScalarBlock
exp2Blk ty ex = do
  tmp <- genUnique
  return$ LL.ScalarBlock [(tmp,ty)] [tmp] [LL.SSet tmp ex]

mkTup :: [Const] -> Const
mkTup [x] = x
mkTup ls  = Tup ls

-- | Insert a list of bindings into a Map
insertAll []         mp = mp
insertAll ((k,v):tl) mp = M.insert k v (insertAll tl mp)
-- Need to test whether this is faster than fromList + union.

