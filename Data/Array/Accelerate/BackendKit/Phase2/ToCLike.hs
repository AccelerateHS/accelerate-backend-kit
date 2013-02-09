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

import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, isTupleTy)
import           Data.Array.Accelerate.BackendKit.CompilerUtils (shapeName)
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike as LL
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.Metadata   (FoldStrides(..), ArraySizeEstimate(..))

import Debug.Trace (trace)

----------------------------------------------------------------------------------------------------

-- | Callback functions for writing results (continuations):
type Cont = [LL.Exp] -> [LL.Stmt]

-- | Unfortunately, this pass needs to do a bit of left-over tuple unzipping
--   too.  For this it carries an environment that maps tupled variables to
--   their detupled subcomponents.  (Note that the same mechanism can also be
--   reused simple to alpha rename vars; i.e. a singleton [Var] list.)
type Env = M.Map Var (Type, Maybe [Var])

----------------------------------------------------------------------------------------------------

-- | This pass takes a SimpleAST IR which already follows a number of
--   conventions that make it directly convertable to the lower level
--   IR, and it does the final conversion.
convertToCLike :: Prog ([(Var,Type)],(FoldStrides Exp, ArraySizeEstimate)) -> LL.LLProg ()
convertToCLike Prog{progBinds,progResults,progType,uniqueCounter,typeEnv} =
  LL.LLProg
  {
    LL.progBinds    = map (fmap (const ())) binds, 
    LL.progResults  = map (copyProp finalEnv) progResults,
    LL.progType     = progType,
    LL.uniqueCounter= newCounter,
    LL.sizeEnv      = sizeEnv
  }
  where
    ((finalEnv,binds),newCounter) = runState (doBinds M.empty progBinds) uniqueCounter

    -- Map subdivided names back onto their original counterparts
    backMap = M.fromList$ concatMap fn (M.toList finalEnv)
    fn (vr,(_,Just ls)) = map (,vr) ls
    fn (_ ,(_,Nothing)) = []

    sizeEnv = M.fromList$ L.concatMap getSize binds
    getSize :: LL.LLProgBind (a,(b,ArraySizeEstimate)) ->
               [(Var,(Type,TrivialExp))]
    getSize (LL.LLProgBind votys (_,(_,sz)) _) =
      let -- Scalars must always have "size" zero:
          mkEntry v t@(TArray _ _) s = (v, (t, s))
          mkEntry v t              _ = (v, (t, TrivConst 0)) in
      case sz of
        KnownSize ls -> zipWith (\ (vo,ty) s -> mkEntry vo ty s) votys (map TrivConst ls)
        UnknownSize  ->
          case votys of 
            [] -> error$ "ToCLike.hs: There should be no forms with ZERO output vars at this phase."
            (v1,_):_ -> 
              let origV = backMap M.! v1  
                  origShp = shapeName origV 
              in case M.lookup origShp finalEnv of
                  -- If we must refer to the size by NAME, that grows complicated if detupling has occured:
                  Just (_, Just shpvs) -> 
                    if length shpvs == length votys
                    then zipWith (\ (vo,ty) shpvr -> mkEntry vo ty (TrivVarref shpvr))
                                  votys shpvs 
                    else error$"ToCLike.hs: internal invariant broken, mismatched len: "++show(votys,shpvs)
                  -- If the shape has not been detupled we can use the original name:
                  Just (_, Nothing) ->
                    case votys of
                      [(vo,ty)] -> [mkEntry vo ty (TrivVarref origShp)]
                      _         -> error$ "ToCLike.hs: invariant broken, expected one output, got "++show votys
                  Nothing -> error$"no entry for shapename "++show origShp++" in final env: "++show finalEnv


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
  tmps <- sequence$ replicate (countVals ty) genUnique
  let binds = zip tmps (flattenTypes ty)
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
      tell$ binds
      let env' = M.insert vr (ty,subcomps) env
          subcomps = Just$ L.map fst binds
          -- subcomps = if isTupleTy ty
          --            then Just$ L.map fst binds
          --            else Nothing 
          a'   = doE env a   
      b'   <- doStmts cont env b
      c'   <- doStmts cont env c

      -- TODO - need to redirect vr to the new vars...
      bod' <- doStmts k env' bod
      return$ LL.SCond a' b' c' :  bod'

    ECond a b c -> fmap sing $ 
      LL.SCond (doE env a) <$> doStmts k env b <*> doStmts k env c

    ELet (vr,ty,rhs) bod ->
      do tell [(vr,ty)]
         let env' = M.insert vr (ty,Nothing) env
         rest <- doStmts k env' bod
         return (LL.SSet vr (doE env rhs) : rest)

    -- An ETuple in tail position:                                 
    ETuple ls -> return$ k$ L.map (doE env) ls 

    -- Anything else had better be just an expression:
    oth -> return$ k [doE env oth]


-- | Return a new list of bindings AND the final environment.
--   May return a shorter list due to copy propagation.
doBinds :: Env -> [ProgBind a] -> GensymM (Env, [LL.LLProgBind a])
doBinds env [] = return (env,[])

-- Reuse the tuple-unzipping machinery to also do copy propagation:
doBinds env (ProgBind vr ty _ (Right (Vr vr2)) : rest) = do
  when (isTupleTy ty) $
    error$ "ToCLike.hs/doBinds: array of tuples should have been desugared long ago: "++show(vr,ty)
  doBinds (M.insert vr (ty,Just [vr2]) env) rest

-- Top-level scalar-tuple binding:  This is the Detupling case.
doBinds env (ProgBind vr ty decor (Left rhs) : rest)
  | isTupleTy ty = do 
    blk@(LL.ScalarBlock _ results _) <- doBlock env rhs
    let componentTys = flattenTypes ty
    -- We split the top-level var into similarly named fresh variables:
    fresh <- replicateM (length componentTys) $ genUniqueWith (show vr)
    let env' = M.insert vr (ty, Just fresh) env
    (env'',rest') <- doBinds env' rest
    return (env'', LL.LLProgBind (zip fresh componentTys)
                                 decor (LL.ScalarCode blk) : rest')
                   
doBinds env (ProgBind vr ty decor rhs : rest) = do 
  rhs' <- case rhs of
            Left  ex -> LL.ScalarCode <$> doBlock env ex
            Right ae -> doAE env ae
  (env',rest') <- doBinds (M.insert vr (ty,Nothing) env) rest

  -- TEMPORARY: We don't yet handle array-of-tuples.  When we do, the (vr,ty) list
  -- will not necessarily be a singleton:
  return (env', LL.LLProgBind [(vr,ty)] decor rhs' : rest')



doAE :: Env -> AExp -> GensymM LL.TopLvlForm
doAE env ae =
  case ae of
    Vr v          -> error$ "ToCLike.hs: Array variable should have been eliminated by copy-prop: "++show v
    Cond a b c    -> return$ LL.Cond (doE env a) b c
    Use  arr      -> return$ LL.Use  arr
    Generate ex (Lam1 (vr,ty) bod) ->
      LL.Generate <$> doBlock env ex
                  <*> (LL.Lam [(vr,ty)] <$> doBlock env' bod)
      where env' = M.insert vr (ty,Nothing) env

    -- TODO: Implement greedy fold/generate fusion RIGHT HERE:
    Fold (Lam2 (v,t) (w,u) bod) ex inV -> do
      let inV' = copyProp env inV
      ix <- genUniqueWith "ix"
      -- TODO: handle the unzipping of arguments:
      LL.GenReduce
        <$> (LL.Lam [(v,t),(w,u)] <$> doBlock env' bod)
        <*> doBlock env ex        
        <*> (LL.Lam [(ix,TInt)] <$> exp2Blk TInt (LL.EIndexScalar inV (LL.EVr ix) 0))
        <*> error "FINISHME - need size here in ToCLike.hs"
        <*> return LL.Fold
        <*> return (error "NEED STRIDE")

      where env' = M.insert v (t,Nothing) $
                   M.insert w (u,Nothing) env

-- TODO/UNFINISHED: Handle other scans and folds... and convert them.
    _ -> error$"ToCLike.hs/doAE: cannot handle array operator:\n"++show(doc ae)


-- Handle simple, non-spine expressions:
doE :: Env -> Exp -> LL.Exp
doE env ex =
  case ex of
    EVr vr           -> case M.lookup vr env of
                         Just (_,Nothing) -> LL.EVr vr
                         Just (_,Just [vr2])   -> LL.EVr vr2
                         Just (_,Just ls) -> error$"ToCLike.hs/doE: uncaught raw reference to tuple-bound variable: "
                                                  ++show vr++" subcomponents "++show ls
                         Nothing -> error$"ToCLike.hs/doE: internal error, var not in env: "++show vr
    ETupProject ind 1 (EVr vr) ->
      case M.lookup vr env of
        Just (_,Just ls) -> LL.EVr$ (reverse ls) !! ind
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

countVals :: Type -> Int
countVals (TTuple ls) = sum$ L.map countVals ls
countVals _           = 1 

flattenTypes :: Type -> [Type]
flattenTypes (TTuple ls) = concatMap flattenTypes ls
flattenTypes oth         = [oth]

sing :: t -> [t]
sing x = [x]

unliftEnv :: M.Map k (b, t) -> M.Map k b
unliftEnv = M.map (\ (t,_) -> t)


-- Do copy propagation for any array-level references:
copyProp :: Env -> Var -> Var
copyProp env vr1 =
  case M.lookup vr1 env of
    -- Array variables have already been detupled, so if there is any entry in
    -- this Env at all, it must be an alias:
    Just (_, Just [vr2]) -> copyProp env vr2
    Just (_, Just ls)    -> error$"ToCLike.hs/copyProp: should not see array variable bound to: "++show ls
    Just _               -> vr1
    Nothing              -> error$"ToCLike.hs/copyProp: internal error, variable "++show vr1++" unbound in environment: "++show (M.keys env)

   
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
