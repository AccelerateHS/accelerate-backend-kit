{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module provides a pass for lifting ELets and (sometimes) EConds.

module Data.Array.Accelerate.BackendKit.Phase2.NormalizeExps (normalizeExps, wrapLets) where
import Control.Monad.Writer
import Control.Applicative ((<$>),(<*>))
import Control.Monad.State.Strict
import Data.Map                   as M

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendKit.Utils.Helpers (mapMAEWithEnv,GensymM, genUnique, genUniqueWith, isTrivialE, dbgPrint)
--------------------------------------------------------------------------------

-- In the process of handling a binding, more might be generated.  The
-- new generated bindings include both original names and the
-- "subcomponent names" for unzipped tuples.
type BindM = WriterT [Binding] GensymM
type Binding = (Var,Type,Exp)
type Env = M.Map Var Type

--------------------------------------------------------------------------------

-- | The main pass.  The resulting program has a "spine" consisting
-- only of ELets and EConds.
-- 
-- After this pass:
--  (1) ELet may not occur in any operand position.
--  (2) ELet may not occur in the RHS of ELet.
--  (3) ECond may not occur in any operand position IF
--      * either of it's branches contains ELet
--      * OR its branches return a tuple type.
--  (4) The index expression of EIndexScalar is trivial. 
normalizeExps :: Prog a -> Prog a 
normalizeExps prog@Prog{progBinds,uniqueCounter} =
  prog{ progBinds= binds, uniqueCounter= newCounter }
 where  
  --binds = runIdentity (doBinds progBinds) 
  env = progToEnv prog
  (binds,newCounter) = runState (doBinds env progBinds) uniqueCounter
   

doBinds :: Env -> [ProgBind t] -> GensymM [ProgBind t]
doBinds env = mapM (doBind env)

doBind :: Env -> ProgBind a -> GensymM (ProgBind a)
doBind env (ProgBind v t dec (Left ex))  = ProgBind v t dec . Left  <$> doSpine env ex
doBind env (ProgBind v t dec (Right ae)) = ProgBind v t dec . Right <$> mapMAEWithEnv env doSpine ae

-- | This lifts out lets but discharges accumulated let bindings before
--   returning, thus returning self-contained expressions.
doSpine :: Env -> Exp -> GensymM Exp
doSpine env ex = 
  case ex of
    EVr _vr               -> return ex
    ETuple els            -> runDischarge (mapM (doE env) els) ETuple    
    ETupProject i l e     -> runDischarge (doE env e)       (ETupProject i l)
    --------------------------------------------------------------------------------    
    EConst _c             -> return ex
    -- EIndexScalar avr indE -> makeTriv env (EIndexScalar avr) indE
    EIndexScalar avr indE -> makeTriv env (EIndexScalar avr) indE
                     
    -- In tail (or "spine") position this conditional is fine.
    ECond e1 e2 e3        -> do (e1',bnds) <- runWriterT$ doE env e1
                                (e2',e3')  <- pairM (doSpine env e2) (doSpine env e3)
                                return$ discharge bnds $ ECond e1' e2' e3'
    -- This is where it gets tricky! 
    -- Do we deal with functions here? OR do we pass them along to some later step?
    -- Do we assure, at this point, that bodys of lambdas have the sought property?
    --Adding a dummy for now 
    EWhile (Lam1 (v1,t1) bod1) (Lam1 (v2,t2) bod2) e ->  
        do 
          let env1 = M.insert v1 t1 env 
          (bod1', bnds1) <- runWriterT$ doE env1 bod1 

          let env2 = M.insert v2 t2 env 
          (bod2', bnds2) <- runWriterT$ doE env2 bod2 

          let bod1'' = discharge bnds1 bod1' 
              bod2'' = discharge bnds2 bod2' 
       
          (e', bnds )  <- runWriterT$ doE env e 
          return (discharge bnds$ EWhile (Lam1 (v1,t1) bod1'') 
                                         (Lam1 (v2,t2) bod2'') e') 

              
                            

                            

-- return ex 
                                              
    -- ELet's may stay as well.  This is the "spine":
    ELet (v,t,rhs) bod    -> do (rhs',bnds) <- runWriterT (doE env rhs)
                                let bnds2 = bnds ++ [(v,t,rhs')]
                                    env'  = M.insert v t env
                                (discharge bnds2 ) <$> doSpine env' bod
    EPrimApp ty p els     -> do (ls',bnds) <- runWriterT$ mapM (doE env) els
                                return (discharge bnds$ EPrimApp ty p ls')
    EShape     _ -> err ex
    EShapeSize _ -> err ex
    EIndex     _ -> err ex

makeTriv :: Env -> (Exp -> Exp) -> Exp -> GensymM Exp
makeTriv env fn indE
  | isTrivialE indE  = runDischarge (doE env indE) fn
  | otherwise        = do let indTy = recoverExpType env indE
                          gensym <- genUniqueWith "liftEIndSclP"
                          runDischarge (doE env indE) $ \ex -> 
                            ELet (gensym,indTy,ex)
                                 (fn (EVr gensym))


-- | In non-tail position we cannot discharge let bindings;
--   we accumulate them using the Writer monad.
doE :: Env -> Exp -> BindM Exp
doE env ex = 
  case ex of
    EVr _vr               -> return ex
    EConst _c             -> return ex    
    ETuple els            -> ETuple <$> mapM (doE env) els
    ETupProject i l e     -> ETupProject  i l <$> doE env e

    -- TODO: Dedup this code:
    EIndexScalar avr indE 
      | isTrivialE indE -> EIndexScalar avr <$> doE env indE 
      | otherwise       -> do let indTy = recoverExpType env indE
                              gensym <- lift$ genUniqueWith "liftEIndScl"
                              ex <- doE env indE
                              tell [(gensym,indTy,ex)]
                              return $ EIndexScalar avr (EVr gensym)


    -- We leave let's inside conditionals, but we might need to lift the conditional itself.    
    ECond e1 e2 e3 -> do e1' <- doE env e1
                         -- Here we potentially do the work TWICE because we don't know what category
                         -- e2/e3 will fall into: allowable as a (non-spine) Exp, or not. 
                         (x,y,bnds) <- lift$ do (x,bnds2) <- runWriterT$ doE env e2
                                                (y,bnds3) <- runWriterT$ doE env e3
                                                return (x,y,bnds2++bnds3)
                         -- We lift out the ECond either due to it containing lets or returning tuples:
                         case (bnds, S.flattenTy (recoverExpType env e2)) of
                           ([],[_]) -> return$ ECond e1' x y 
                           -- Otherwise the rule is that the ECond can stay part of the 
                           -- "spine" if it is lifted into the RHS of a let binding:
                           _  -> do gensym <- lift$ genUnique
                                    enew   <- lift$ ECond e1' <$> doSpine env e2 <*> doSpine env e3
                                    tell [(gensym, recoverExpType env ex, enew)]
                                    return (EVr gensym)

    -- Not a dummy anymore
    EWhile (Lam1 (v1,t1)  bod1) (Lam1 (v2,t2) bod2) e -> 
        do 
          bod1' <- doE (M.insert v1 t1 env) bod1 
          bod2' <- doE (M.insert v2 t2 env) bod2
          e'    <- doE env e 
          return $ EWhile (Lam1 (v1,t1) bod1') (Lam1 (v2,t2) bod2') e' 


    -- Non-spine ELet's are lifted out:
    ELet (v,t,rhs) bod    -> do rhs' <- doE env rhs
                                -- Inject new bindings for untupled scalars vars:
                                tell [(v,t,rhs')]
                                -- NOTE! The order that bindings are accumulate ensures that
                                -- any bindings emitted by tells BEFORE this point are in-scope.
                                -- In particular, 'v' is now in-scope for any bindings emitted
                                -- while processing 'bod' below:
                                doE (M.insert v t env) bod
    EPrimApp ty p els     -> EPrimApp ty p <$> mapM (doE env) els
    EShape     _ -> err ex
    EShapeSize _ -> err ex
    EIndex     _ -> err ex

----------------------------------------------------------------------------------------------------
-- Small Helpers:

-- | Discharge floated let bindings by introducing ELets:
runDischarge :: BindM a -> (a -> Exp) -> GensymM Exp
runDischarge m k = 
  do (x,bnds) <- runWriterT m
     return$ discharge bnds (k x)

pairM :: Monad m => m a -> m b -> m (a,b)
pairM ma mb = do x <- ma 
                 y <- mb
                 return (x,y)

discharge :: [Binding] -> Exp -> Exp
discharge = wrapLets

wrapLets :: [Binding] -> Exp -> Exp
wrapLets []                bod = bod
wrapLets ((v,t,rhs) :rest) bod = ELet (v,t,rhs) $ discharge rest bod


err :: Show a => a -> t
err ex = error$"NormalizeExps.hs: this form should have been desugared before this pass: "++show ex

--------------------------------------------------------------------------------
