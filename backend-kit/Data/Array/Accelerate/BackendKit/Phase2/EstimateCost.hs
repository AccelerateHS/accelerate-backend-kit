{-# LANGUAGE NamedFieldPuns, DeriveGeneric #-}
-- GeneralizedNewtypeDeriving
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Data.Array.Accelerate.BackendKit.Phase2.EstimateCost (estimateCost, Cost(Cost)) where 

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.List as L
import Data.Array.Accelerate.BackendKit.Utils.Helpers
import Data.Array.Accelerate.BackendKit.IRs.Metadata (Uses(..), ArraySizeEstimate(..))

import Text.PrettyPrint.GenericPretty (Out, Generic)

data Cost = Cost Int
  deriving (Generic, Show)
instance Out Cost

estimateCost :: Prog (ArraySizeEstimate) -> Prog (ArraySizeEstimate,Cost)
-- estimateCost = fmap (\(a,b) -> (a,b,Cost 0)) 
estimateCost prog@Prog{progBinds} =
  prog{ progBinds= L.map doBind progBinds}

-- doBind pb@(ProgBind _ _ _ (Left _))   = fmap (\d -> (d,FreeVars S.empty)) pb

doBind :: ProgBind a -> ProgBind (a, Cost)
-- This pass measures KERNEL free vars, these scalar expressions don't count:
doBind (ProgBind v t a (Left ex))  = ProgBind v t (a,Cost (doE  ex)) (Left ex)
doBind (ProgBind v t a (Right ae)) = ProgBind v t (a,Cost (doAE ae)) (Right ae)


-- Update a usemap with new usages found in an AExp.
doAE :: AExp -> Int
doAE ae =
  case ae of
    Use _                      -> 0
    Use' _ _ _                 -> 0
    Vr _                       -> 0
    Cond _ _  _                -> 0
    Map (Lam1 _ e) _           -> doE e
    ZipWith (Lam2 _ _ e) _ _   -> doE e
    Backpermute _ (Lam1 _ e) _ -> doE e
    Generate _ (Lam1 _ e)      -> doE e
    
    -- The costs are not particularly well defined for an operator with TWO bodies like this:
    Permute    (Lam2 _ _ bod1) _ (Lam1 _ bod2) _ -> doE bod1 + doE bod2
    Fold  (Lam2 _ _ bod) _ _        -> doE bod
    Fold1 (Lam2 _ _ bod) _          -> doE bod
    FoldSeg   (Lam2 _ _ bod) _ _ _  -> doE bod
    Fold1Seg  (Lam2 _ _ bod) _ _    -> doE bod
    Scanl  (Lam2 _ _ bod) _ _       -> doE bod
    Scanl' (Lam2 _ _ bod) _ _       -> doE bod
    Scanl1 (Lam2 _ _ bod)     _     -> doE bod
    Scanr  (Lam2 _ _ bod) _ _       -> doE bod
    Scanr' (Lam2 _ _ bod) _ _       -> doE bod
    Scanr1 (Lam2 _ _ bod)    _      -> doE bod
    Stencil  (Lam1 _ bod) _ _       -> doE bod
    Stencil2 (Lam2 _ _ bod) _ _ _ _ -> doE bod
    Unit _e                    -> err
    Reshape _ _                -> err
    Replicate _ _ _            -> err
    Index _ _ _                -> err      
 where 
  err = error$ "EstimateCost: the following should be desugared before this pass is called:\n   "++ show (ae)
    

doE :: Exp -> Int
doE ex =
  case ex of
    EVr vr              -> 0
    EConst c            -> costConst c
    EIndexScalar avr ex -> derefCost + doE ex
    ECond e1 e2 e3      -> ifCost + doE e1 + doE e2 + doE e3
    EWhile (Lam1 _ bod1) (Lam1 _ bod2) e -> doE e + doE bod1 + doE bod2
    ELet (v,_,rhs) bod  -> doE rhs + doE bod
    ETupProject _ _ ex  -> doE ex
    -- TODO: ideally we would estimate the different cost of primitives:
    EPrimApp p _ els    -> 1 + doEs els 
    EShapeSize ex       -> 1 + doE ex     
    ETuple els          -> doEs els        
    EIndex els          -> doEs els 
    EShape avr          -> 1 
 where
  doEs ls = sum (map doE ls)

