{-# Language NamedFieldPuns, TupleSections #-}
{-# Language ParallelListComp #-}

module Data.Array.Accelerate.BackendKit.Phase2.UnzipArrays (unzipArrays) where
import Control.Monad.State.Strict
import Control.Applicative ((<$>),(<*>), pure)
import qualified Data.Map              as M

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendKit.Utils.Helpers ((#),isTrivialE, GensymM, maybeLetE)
import Data.Array.Accelerate.BackendKit.IRs.Metadata (SubBinds(..), OpInputs(..))
import Data.Array.Accelerate.BackendKit.CompilerUtils (maybtrace)
--------------------------------------------------------------------------------


-- | This pass commits to unzipped arrays.  It makes the leap between referring to
-- arrays in their zipped (array of tuples) form to their unzipped components.
-- 
-- Alas, because we are stuck with the Prog IR at this juncture, we yet can't fully
-- rewrite the AST to reflect this change..  However, after this pass the regular
-- variable fields of array op `ProgBinds` are IGNORED and the REAL names are found
-- in the SubBinds decorators.
--
-- Another way that we draw outside the lines of the Prog type, is that we nuke the
-- INPUTS to array operators.  Those refer, naturally, to the pre-unzipped arrays.
-- Instead we list the inputs explicitly in a new decoration.  Scalar expression
-- arguments to array operators are left alone, and they may still be tuples
-- (e.g. the initial element of a Fold).
--
-- Also, this pass does copy-prop at the array level.  After this pass array level
-- `Vr` should not occur.
--
-- This pass eliminates ETupProject's around EIndexScalar's.
unzipArrays :: S.Prog (SubBinds,a) -> S.Prog (OpInputs,(SubBinds,a))
unzipArrays prog@Prog{progBinds,progResults = WithShapesUnzipped pR, uniqueCounter, typeEnv } =
  prog { progBinds   = binds',
         -- All parts of an unzipped array have the same shape:         
         progResults = WithShapesUnzipped$
                       concatMap (\ (v,s) -> map (,s) (env # v)) pR,
         -- Note: typeEnv already has the unzipped types.
         uniqueCounter = cntr'
       }
  where
    (binds',cntr') = runState (doBinds typeEnv M.empty progBinds) uniqueCounter
    env = M.fromList$
          map (\(ProgBind v _ (SubBinds vrs _,_) _) -> (v,vrs)) progBinds

-- | For this pass every top level binding is tracked in the environment which is
-- passed throuh the helper functions.
type Env = M.Map Var [Var]
type TEnv = M.Map Var Type

doBinds :: TEnv -> Env -> [ProgBind (SubBinds,a)] -> GensymM [ProgBind (OpInputs,(SubBinds,a))]
doBinds _ _ [] = return [] 
doBinds tenv env (ProgBind vo _ _ (Right (Vr v1)) : rest) =
  -- Copy propagataion:
  doBinds tenv (M.insert vo (env#v1) env) rest

-- Unzip Use to make things easier for future passes:
doBinds tenv env (ProgBind vo aty (SubBinds {subnames,arrsize},d2)
             (Right (Use (AccArray {arrDim,arrPayloads}))) : rest) 
  | length subnames > 1 =
    ([ ProgBind subname arrty
                (OpInputs [], (SubBinds {subnames=[subname], arrsize=arrsize},d2))
                (Right (Use (AccArray { arrDim, arrPayloads = [onepayl] })))
     | subname <- subnames
     | arrty   <- S.flattenArrTy aty
     | onepayl <- arrPayloads  
     ]++)
    <$> doBinds tenv (M.insert vo subnames env) rest

doBinds tenv env (ProgBind vo ty dec@(SubBinds {subnames},_) op : rest) = do
  (dec',op') <-
      case op of
        Left  ex -> do ex' <- doE tenv env ex
                       return (OpInputs[], Left ex')
        Right ae -> do (ls,ae') <- doAE tenv env ae
                       return (OpInputs ls,Right ae')
  (ProgBind nukedVar ty (dec',dec) op' :)
    <$> doBinds tenv (M.insert vo subnames env) rest

-- | Returns (unzipped) operator INPUTS.
doAE :: TEnv -> Env -> AExp -> GensymM ([[Var]], AExp)
doAE tenv env ae = 
  case ae of
    Use _               -> return ([],ae)
    Cond a b c          -> do a' <- (exp a)
                              return ([sp b,sp c], Cond a' nukedVar nukedVar)
    Generate e lam1     -> do l1 <- doLam1 tenv lam1
                              e' <- (exp e)
                              return ([], Generate e' l1)
    Fold lam2 e v       -> do l2 <- doLam2 tenv lam2
                              e' <- (exp e)
                              return ([sp v],Fold l2 e' nukedVar)
    Fold1    lam2 v     -> do l2 <- doLam2 tenv lam2
                              return ([sp v],Fold1 l2 nukedVar)
    FoldSeg  lam2 e v w -> do l2 <- doLam2 tenv lam2
                              e' <- (exp e)
                              return ([sp v,sp w],FoldSeg l2 e' nukedVar nukedVar)
    Fold1Seg lam2 v w   -> do l2 <- doLam2 tenv lam2
                              return ([sp v,sp w],Fold1Seg l2        nukedVar nukedVar)
    Scanl    lam2 e v   -> do l2 <- doLam2 tenv lam2
                              x  <- (exp e)
                              return ([sp v],Scanl  l2 x nukedVar)
    Scanl'   lam2 e v   -> do l2 <- doLam2 tenv lam2
                              e' <- (exp e)
                              return ([sp v],Scanl' l2 e' nukedVar)
    Scanl1   lam2   v   -> do l2 <- doLam2 tenv lam2
                              return ([sp v],Scanl1 l2         nukedVar)
    Scanr    lam2 e v   -> do l2 <- doLam2 tenv lam2
                              e' <- (exp e)
                              return ([sp v],Scanr  l2 e' nukedVar)
    Scanr'   lam2 e v   -> do l2 <- doLam2 tenv lam2
                              e' <- exp e
                              return ([sp v],Scanr' l2 e' nukedVar)
    Scanr1   lam2   v   -> do l2 <- doLam2 tenv lam2
                              return ([sp v],Scanr1 l2         nukedVar)
    Stencil  lam1 b v   -> do l1 <- doLam1 tenv lam1
                              return ([sp v],Stencil l1 b nukedVar)
    Stencil2 l2 b v c w -> do l2' <- (doLam2 tenv l2)
                              return ([sp v,sp w],Stencil2 l2' b nukedVar c nukedVar)
    Permute l2 v l1 w   -> do l2' <- (doLam2 tenv l2)
                              l1' <- (doLam1 tenv l1)
                              return ([sp v,sp w],Permute l2' nukedVar l1' nukedVar)
    Unit {}             -> err ae
    Map  {}             -> err ae
    ZipWith {}          -> err ae
    Backpermute {}      -> err ae
    Replicate {}        -> err ae
    Reshape   {}        -> err ae
    Index     {}        -> err ae
    Vr _                -> error "impossible, but GHC doesn't know it"
 where
   sp v = case M.lookup v env of
            Nothing -> error$"UnzipArrays.hs/doAE: could not find SubBinds for "++show v
            Just x  -> x
   exp = doE tenv env
   -- We're NOT detupling scalar vars at this point, so we don't bother extending the env:
   doLam1 tenv (Lam1 (v,ty) bod) = Lam1 (v,ty) <$> doE tenv env bod
   doLam2 tenv (Lam2 b1 b2 bod)  = Lam2 b1 b2  <$> doE tenv env bod

doE :: TEnv -> Env -> Exp -> GensymM Exp
doE tenv env ex =
  case ex of
    ETupProject ix len (EIndexScalar avr ind) ->
      if len /= 1 then error$"UnzipArrays.hs: ETupProject with len/=1: "++show ex
      else
        maybtrace ("Projecting out of "++show (env # avr)++" for avr "++show avr++" want index "++show ix)$
        EIndexScalar (reverse (env # avr) !! ix) <$> (doE tenv env ind)
    EIndexScalar avr e -> 
      do let ixty = recoverExpType tenv e
         e' <- fn e
         -- We may be forced to create an ETuple here, but it must be in tail position.
         maybeLetE e' ixty $ \ e'' ->
           mkETuple [ EIndexScalar avr' e'' | avr' <- env#avr ]
          
    ETupProject ix l e  -> ETupProject ix l <$> fn e
    EShape _            -> err ex
    EShapeSize _        -> err ex
    EIndex _            -> err ex
    EConst _            -> return ex
    EVr _               -> return ex
    ECond e1 e2 e3      -> ECond <$> fn e1 <*> fn e2 <*> fn e3
    ELet (v,t,rhs) bod  -> do rhs' <- fn rhs
                              ELet (v,t,rhs') <$> fn bod
    ETuple els          -> ETuple       <$> mapM fn els
    EPrimApp p t els    -> EPrimApp p t <$> mapM fn els
 where
    fn = doE tenv env

err :: Show a => a -> b
err x = error$"UnzipArrays.hs: should have been eliminated before this pass: "++ show x

nukedVar :: Var
nukedVar = var ""
