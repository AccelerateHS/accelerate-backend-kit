{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Array.Accelerate.BackendKit.Phase2.InlineCheap (inlineCheap) where 
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec))
import Data.Map as M hiding (map) 

import Data.Array.Accelerate.BackendKit.Utils.Helpers (defaultDupThreshold)
import Data.Array.Accelerate.BackendKit.IRs.Metadata  (Uses(..), ArraySizeEstimate(..))
import Data.Array.Accelerate.BackendKit.Phase2.EstimateCost (Cost(Cost))

-- | This pass serves two purposes:
--   (1) inlines any Generate expressions 
--   (2) does copy-propagation at the array level (cost 0 inlining)
inlineCheap :: Prog (ArraySizeEstimate,Cost) -> Prog ArraySizeEstimate
inlineCheap prog@Prog{progBinds, progResults} =
  prog{ progBinds  = map (doBind env) progBinds, 
        progResults= map (copyProp env) progResults }
 where
  env = M.fromList$ map (\ pb@(ProgBind v _ _ _) -> (v,pb)) progBinds  


-- Do copy propagation for any array-level references:
-- copyProp :: Int -> Int -> Int
copyProp :: Map Var (ProgBind (a,Cost)) -> Var -> Var
copyProp env vr = case env M.! vr of 
                    ProgBind _ _ _ (Right (Vr upV)) -> copyProp env upV
                    _ -> vr


doBind :: Map Var (ProgBind (a,Cost)) -> ProgBind (a,Cost) -> ProgBind a
doBind mp (ProgBind v t (a,_) (Left ex))  = ProgBind v t a (Left  (doEx mp ex))
doBind mp (ProgBind v t (a,_) (Right ae)) = ProgBind v t a (Right (doAE mp ae))

-- Update a usemap with new usages found in an AExp.
doAE :: Map Var (ProgBind (a,Cost)) -> AExp -> AExp
doAE mp ae =
  case ae of
    Use _                             -> ae
    Vr v                              -> Vr$ cp v
    Cond a b c                        -> Cond (doE a) (cp b) (cp c)
    Generate e (Lam1 arg bod)         -> Generate (doE e) (Lam1 arg (doE bod))
    Stencil  (Lam1 a1    bod) b v     -> Stencil  (Lam1 a1    (doE bod)) b (cp v)
    Stencil2 (Lam2 a1 a2 bod) b v c w -> Stencil2 (Lam2 a1 a2 (doE bod)) b (cp v) c (cp w)
    Fold     (Lam2 a1 a2 bod) e v     -> Fold     (Lam2 a1 a2 (doE bod)) (doE e) (cp v)
    Fold1    (Lam2 a1 a2 bod) v       -> Fold1    (Lam2 a1 a2 (doE bod)) (cp v)
    FoldSeg  (Lam2 a1 a2 bod) e v w   -> FoldSeg  (Lam2 a1 a2 (doE bod)) (doE e) (cp v) (cp w)
    Fold1Seg (Lam2 a1 a2 bod) v w     -> Fold1Seg (Lam2 a1 a2 (doE bod)) (cp v) (cp w)
    Scanl    (Lam2 a1 a2 bod) e v     -> Scanl    (Lam2 a1 a2 (doE bod)) (doE e) (cp v)
    Scanl'   (Lam2 a1 a2 bod) e v     -> Scanl'   (Lam2 a1 a2 (doE bod)) (doE e) (cp v)
    Scanl1   (Lam2 a1 a2 bod)   v     -> Scanl1   (Lam2 a1 a2 (doE bod))         (cp v)
    Scanr    (Lam2 a1 a2 bod) e v     -> Scanr    (Lam2 a1 a2 (doE bod)) (doE e) (cp v)
    Scanr'   (Lam2 a1 a2 bod) e v     -> Scanr'   (Lam2 a1 a2 (doE bod)) (doE e) (cp v)
    Scanr1   (Lam2 a1 a2 bod)   v     -> Scanr1   (Lam2 a1 a2 (doE bod))         (cp v)
    Permute (Lam2 a1 a2 bod1) v (Lam1 a3 bod2) w -> Permute (Lam2 a1 a2 (doE bod1)) (cp v)
                                                            (Lam1 a3    (doE bod2)) (cp w)
    Map _ _           -> err
    ZipWith _ _ _     -> err
    Unit _            -> err
    Backpermute _ _ _ -> err
    Reshape _ _       -> err
    Replicate _ _ _   -> err
    Index _ _ _       -> err      
 where err = doerr ae
       doE = doEx mp
       cp  = copyProp mp

doerr e = error$ "InlineCheap: the following should be desugared before this pass is called:\n   "++ show (doc e)
    

doEx :: Map Var (ProgBind (a,Cost)) -> Exp -> Exp
doEx mp ex = 
  case ex of
    -- Where we reference other arrays is where inlining may occur:
    EIndexScalar avr ex -> let pb  = mp ! avr
                               ex' = doE ex in
                           -- This will also do copyProp, btw:
                           if getCost pb <= defaultDupThreshold then 
                              case inline pb ex' of
                                Nothing -> EIndexScalar avr ex'
                                -- Reprocess the result of inlining:
                                Just x  ->
                                  maybtrace ("!! Victory, inlineCheap: inlining reference to "++show avr) $
                                  doEx mp x 
                           else EIndexScalar avr ex'
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
  


