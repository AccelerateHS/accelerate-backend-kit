{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Array.Accelerate.BackendKit.Phase2.InlineCheap (inlineCheap) where 
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.CompilerUtils (maybtrace)
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec))
import Data.Map as M hiding (map)
import Control.Applicative ((<$>),(<*>))
import Control.Monad.State.Strict (runState)

import Data.Array.Accelerate.BackendKit.Utils.Helpers (defaultDupThreshold,GensymM,mapMAE)
import Data.Array.Accelerate.BackendKit.IRs.Metadata  (ArraySizeEstimate(..))
import Data.Array.Accelerate.BackendKit.Phase2.EstimateCost (Cost(Cost))

-- | This pass serves two purposes inlines `Generate` into their consumers, if the
-- computation in their bodies are deemed cheap.
inlineCheap :: Prog (ArraySizeEstimate,Cost) -> Prog ArraySizeEstimate
inlineCheap prog@Prog{progBinds, progResults, uniqueCounter } =
  prog{ progBinds  = newbinds, 
        progResults= map (copyProp env) progResults,
        uniqueCounter= newCount }
 where
  env = M.fromList$ map (\ pb@(ProgBind v _ _ _) -> (v,pb)) progBinds  
  (newbinds,newCount) =
    runState (mapM (doBind env) progBinds) uniqueCounter



-- Do copy propagation for any array-level references:
-- copyProp :: Int -> Int -> Int
copyProp :: Map Var (ProgBind (a,Cost)) -> Var -> Var
copyProp env vr = case env M.! vr of 
                    ProgBind _ _ _ (Right (Vr upV)) -> copyProp env upV
                    _ -> vr


doBind :: Map Var (ProgBind (a,Cost)) -> ProgBind (a,Cost) -> GensymM (ProgBind a)
doBind mp (ProgBind v t (a,_) (Left ex))  = ProgBind v t a . Left <$> return (doEx mp ex)
doBind mp (ProgBind v t (a,_) (Right ae)) = ProgBind v t a . Right <$> doAE mp ae

-- Update a usemap with new usages found in an AExp.
doAE :: Map Var (ProgBind (a,Cost)) -> AExp -> GensymM AExp
doAE mp ae = 
  case ae of
    Map _ _           -> err
    ZipWith _ _ _     -> err
    Unit _            -> err
    Backpermute _ _ _ -> err
    Reshape _ _       -> err
    Replicate _ _ _   -> err
    Index _ _ _       -> err
    _                 -> mapMAE (return . doEx mp) ae
 where err = doerr ae

doerr :: Out a => a -> t
doerr e = error$ "InlineCheap: the following should be desugared before this pass is called:\n   "++ show (doc e)
    

doEx :: Map Var (ProgBind (a,Cost)) -> Exp -> Exp
doEx mp ex = 
  case ex of
    -- Where we reference other arrays is where inlining may occur:
    ---------------------------------------------------------------
    EIndexScalar avr ex -> let pb  = mp ! avr
                               ex' = doE ex in
                           -- This will also do copyProp, btw:
                           if getCost pb <= defaultDupThreshold then 
                              case inline pb ex' of
                                Nothing -> EIndexScalar avr ex'
                                -- Reprocess the result of inlining:
                                Just code ->
                                  maybtrace ("!! Victory, inlineCheap: inlining reference to "++show avr) $
                                  doEx mp code -- (freshenExpNames code)
                                  
                           else EIndexScalar avr ex'
    ---------------------------------------------------------------                             
    EVr vr              -> ex
    EConst c            -> ex
    ECond e1 e2 e3      -> ECond (doE e1) (doE e2) (doE e3)
    ELet (v,t,rhs) bod  -> ELet (v,t,doE rhs) (doE bod)
    ETupProject i l ex  -> ETupProject i l (doE ex)
    EPrimApp p t els    -> EPrimApp p t (map doE els)
    ETuple els          -> ETuple (map doE els)
    EShapeSize ex       -> doerr ex    
    EShape avr          -> doerr ex
    EIndex els          -> doerr ex
 where
   -- Inline ONLY low-cost generates and variable refs:
   inline (ProgBind _ _ _ (Right (Generate ex (Lam1 (v,ty) bod)))) indE = 
      Just$ ELet (v,ty,indE) (doE bod)
   inline (ProgBind _ _ _ (Right (Vr vrUp))) indE = Just$ EIndexScalar vrUp indE   
   inline _ _ = Nothing
   
   doE = doEx mp   
   getCost (ProgBind _ _ (_,Cost c) _) = c
  


