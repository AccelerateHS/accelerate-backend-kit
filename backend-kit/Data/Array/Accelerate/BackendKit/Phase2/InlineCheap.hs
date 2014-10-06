{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Array.Accelerate.BackendKit.Phase2.InlineCheap (inlineCheap) where 
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec))
import Data.Map as M hiding (map)
import Control.Applicative ((<$>),(<*>))
import Control.Monad.State.Strict (runState)

import Data.Array.Accelerate.BackendKit.Utils.Helpers (maybtrace, defaultDupThreshold,GensymM,mapMAE, (#))
import Data.Array.Accelerate.BackendKit.IRs.Metadata  (ArraySizeEstimate(..))
import Data.Array.Accelerate.BackendKit.Phase2.EstimateCost (Cost(Cost))

-- | This pass inlines `Generate` into their consumers, if the
-- computation in their bodies are deemed cheap.
inlineCheap :: Prog (ArraySizeEstimate,Cost) -> Prog ArraySizeEstimate
inlineCheap prog@Prog{progBinds, progResults, uniqueCounter } =
  let WithShapes pR = progResults
      (pRN,pRS) = unzip pR in 
  prog{ progBinds  = newbinds, 
        progResults= WithShapes $ zip (map (copyProp env) pRN) pRS,
        uniqueCounter= newCount }
 where
  env = M.fromList$ map (\ pb@(ProgBind v _ _ _) -> (v,pb)) progBinds  
  (newbinds,newCount) =
    runState (mapM (doBind env) progBinds) uniqueCounter



-- Do copy propagation for any array-level references:
-- copyProp :: Int -> Int -> Int
copyProp :: Show a => Map Var (ProgBind (a,Cost)) -> Var -> Var
copyProp env vr = case env # vr of 
                    ProgBind _ _ _ (Right (Vr upV)) -> copyProp env upV
                    _ -> vr


doBind :: Show a => Map Var (ProgBind (a,Cost)) -> ProgBind (a,Cost) -> GensymM (ProgBind a)
doBind mp (ProgBind v t (a,_) (Left ex))  = ProgBind v t a . Left  <$> doEx mp ex
doBind mp (ProgBind v t (a,_) (Right ae)) = ProgBind v t a . Right <$> doAE mp ae

-- Update a usemap with new usages found in an AExp.
doAE :: Show a => Map Var (ProgBind (a,Cost)) -> AExp -> GensymM AExp
doAE mp ae = 
  case ae of
    Map _ _           -> err
    ZipWith _ _ _     -> err
    Unit _            -> err
    Backpermute _ _ _ -> err
    Reshape _ _       -> err
    Replicate _ _ _   -> err
    Index _ _ _       -> err
    _                 -> mapMAE (doEx mp) ae
 where err = doerr ae

doerr :: Out a => a -> t
doerr e = error$ "InlineCheap: the following should be desugared before this pass is called:\n   "++ show (doc e)
    

doEx :: Show a => Map Var (ProgBind (a,Cost)) -> Exp -> GensymM Exp
doEx mp ex = 
  case ex of
    -- Where we reference other arrays is where inlining may occur:
    ---------------------------------------------------------------

    EIndexScalar avr ex -> do
      let pb  = mp # avr
      ex' <- doE ex 
      if getCost pb <= defaultDupThreshold then do
         mb <- inline pb ex'
         case mb of
           Nothing -> return$ EIndexScalar avr ex'
           -- Reprocess the result of inlining:
           Just code -> do
             code' <- freshenExpNames code
             maybtrace ("!! Victory, inlineCheap: inlining reference to "++show avr) $
              doEx mp code'
       else return$ EIndexScalar avr ex'

    -- Boilerplate:     
    ----------------------------------------
    EVr _               -> return ex
    EConst _            -> return ex
    ECond e1 e2 e3      -> ECond   <$> doE e1 <*> doE e2 <*> doE e3
    EWhile (Lam1 a1 bod1) (Lam1 a2 bod2) e -> EWhile <$> (Lam1 a1 <$> doE bod1) 
                                                     <*> (Lam1 a2 <$> doE bod2)  
                                                     <*> doE e
    ELet (v,t,rhs) bod  -> (\r b -> ELet (v,t,r) b) <$> doE rhs <*> doE bod
    ETupProject i l e   -> ETupProject i l  <$> doE e
    EPrimApp p t els    -> EPrimApp    p t  <$> mapM doE els
    ETuple els          -> ETuple           <$> mapM doE els
    EIndex _            -> doerr ex
    EShapeSize ex       -> doerr ex 
    EShape avr          -> doerr ex
    
 where
   -- Inline ONLY low-cost generates and variable refs:
   inline (ProgBind _ _ _ (Right (Generate ex (Lam1 (v,ty) bod)))) indE = 
      Just . ELet (v,ty,indE) <$> doE bod

-- TODO: inline references to USE'd arrays, if the index is avialable.

   inline (ProgBind _ _ _ (Right (Vr vrUp))) indE = return (Just$ EIndexScalar vrUp indE)
   inline _ _ = return Nothing
   
   doE = doEx mp   
   getCost (ProgBind _ _ (_,Cost c) _) = c
  


