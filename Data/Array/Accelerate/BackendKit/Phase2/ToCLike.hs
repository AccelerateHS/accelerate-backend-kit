{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This pass does the final conversion to CLike IR format.  Unfortunately it
--   does more work than that along the way.  In particular it finishes the rest of
--   the unzipping process, and incidentally does copy-prop.

module Data.Array.Accelerate.BackendKit.Phase2.ToCLike (convertToCLike) where

import qualified Data.Map   as M
import           Data.List  as L
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

import Debug.Trace (trace)

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
  LL.LLProg
  {
    LL.progBinds    = map (fmap (const ())) binds, 
--    LL.progResults  = map (copyProp finalEnv) progResults,
    LL.progResults  = progResults,
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
      M.union (M.fromList$ zip vrs$ zip (S.flattenTy elt) (repeat triv))
              acc
    red acc _ = acc
      

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
  
-- | This takes a continuation for where to write the results.
--
-- Returns:
--  (1) list of vars where the final return values reside
--  (2) a list of statements encoding the computation
doStmts :: Cont -> Env -> Exp ->
           WriterT [(Var,Type)] GensymM [LL.Stmt]
doStmts k env ex =
  case ex of    
    ELet (vr,ty, ECond a b c) bod  -> do
      -- Introduce a new temporaries and a continuation for the non-tail conditional:
      (binds,cont) <- lift$ makeResultWriterCont ty
      mytell$ binds
      
      let env' = M.insert vr (ty,subcomps,Nothing) env
          subcomps = L.map fst binds
          a'   = doE env a   
      b'   <- doStmts cont env b
      c'   <- doStmts cont env c
      -- These are only partial continuations.  Still need to call ours, 'k':
      bod' <- doStmts k env' bod
      return$ LL.SCond a' b' c' :  bod'

    ELet (vr,ty,rhs) bod ->
      do mytell [(vr,ty)]
         let env' = M.insert vr (ty,[vr],Nothing) env
         rest <- doStmts k env' bod
         return (LL.SSet vr (doE env rhs) : rest)

    ECond a b c -> fmap sing $ 
      LL.SCond (doE env a) <$> doStmts k env b <*> doStmts k env c

    -- An ETuple in tail position:                                 
    ETuple ls -> return$ k$ L.map (doE env) ls 

    -- Anything else had better be just an expression in the new IR:
    oth -> return$ k [doE env oth]
 where
   mytell ls =
     if any isTupleTy (map snd ls)
     then error$"ToCLike.hs: internal error, tupled type still remaining in bindings: "++show ls
     else tell ls

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

       Generate ex (Lam1 (vr,ty) bod) -> do
         -- Because arrays are 1D at this point, ex and vr are scalar.
         -- 'ex' should be of type TInt, and it should be trivial.
         let env' = M.insert vr (ty,[vr],error"SIZE") env
         LL.GenManifest <$>
           LL.Gen (doTriv ex)
             <$> (LL.Lam [(vr,ty)] <$> doBlock env' bod)

       -- TODO: Implement greedy fold/generate fusion RIGHT HERE:
       Fold  lam2 ex _     -> foldHelp (head vis) LL.StrideAll lam2 =<< (LL.Fold <$> doBlock env ex)
       FoldSeg lam2 ex _ _ -> do let [inVs,segVs] = vis
                                     Just (StrideConst strideE) = foldstride
                                 initSB <- doBlock env ex 
                                 foldHelp inVs (StrideConst$ doE env strideE) lam2
                                   (LL.FoldSeg initSB (LL.Manifest segVs))
       Fold1    {}     -> err
       Fold1Seg {}     -> err
       Scanl lam2 ex _ -> foldHelp (head vis) LL.StrideAll lam2 =<< (LL.Scan LL.LeftScan  <$> doBlock env ex)
       Scanr lam2 ex _ -> foldHelp (head vis) LL.StrideAll lam2 =<< (LL.Scan LL.RightScan <$> doBlock env ex)    
       Scanl1 {}       -> err
       Scanr1 {}       -> err
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
        Just (_,ls,_) -> LL.EVr$ (reverse ls) !! ind
        oth -> error$"ToCLike.hs/doE: internal error, tuple project of field "++show ind++
                     " of var: "++show vr++", env binding: "++show oth

    ETupProject _ _ _ -> error"FINISHME -- ETupProject"
    
    EConst c         -> LL.EConst$ mkTup$ flattenConst c
    EPrimApp ty p ls -> LL.EPrimApp ty p $ L.map (doE env) ls
    ECond a b c      -> LL.ECond (doE env a) (doE env b) (doE env c)
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

flattenConst :: Const -> [Const]
flattenConst (Tup ls) = concatMap flattenConst ls
flattenConst c        = [c]

mkTup :: [Const] -> Const
mkTup [x] = x
mkTup ls  = Tup ls

-- | Insert a list of bindings into a Map
insertAll []         mp = mp
insertAll ((k,v):tl) mp = M.insert k v (insertAll tl mp)
-- Need to test whether this is faster than fromList + union.

-- Flatting that handles either array or scalar types.
flattenEither :: Type -> [Type]
flattenEither ty@(TArray _ _) = S.flattenArrTy ty
flattenEither ty              = S.flattenTy ty

