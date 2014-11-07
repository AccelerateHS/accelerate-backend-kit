{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module defines a compiler pass for counting variable uses.

module Data.Array.Accelerate.BackendKit.Phase2.TrackUses (trackUses, Uses(..),
                  doE, doAE
                 ) where

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc  as T
import Data.List as L
import Data.Map  as M
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import Data.Array.Accelerate.BackendKit.IRs.Metadata (Uses(..))

conservativeMode = False

-- | A compiler pass that adds metadata only.  It counts the uses of
--   all array and scalar variables.  
trackUses :: Prog a -> Prog (a, Uses)
trackUses prog@Prog{progBinds, progResults} =
  prog { progBinds= L.map (decorBind allUses) progBinds}
 where
  initUses  = if conservativeMode
              then M.fromList $ L.map (\ (ProgBind vr _ _ _) -> (vr,Uses 0 0)) progBinds
              else M.empty
  withFinal = L.foldl (flip addArrRef) initUses (T.resultNames progResults)
  allUses   = L.foldl gatherUses withFinal progBinds

-- | Helper function to fold over binds and collect uses.
gatherUses :: UseMap -> ProgBind a -> UseMap
gatherUses mp (ProgBind _vr _ty _dec (Right ae)) = doAE ae mp
gatherUses mp (ProgBind _vr _ty _dec (Left  ex)) = doE  ex mp

-- | Add the final usage numbers back to the binding decorations.
decorBind :: UseMap -> ProgBind a -> ProgBind (a, Uses)
decorBind finalMp (ProgBind vr ty dec exp) =
  ProgBind vr ty (dec, uses) exp
 where
   uses = case M.lookup vr finalMp of
            Nothing -> if conservativeMode
                       then error ("trackUses: should be an entry for variable: "++show vr)
                       else Uses 0 0
            Just u  -> u 

type UseMap = M.Map Var Uses

-- | Register an array reference.
addArrRef :: Var -> UseMap -> UseMap
addArrRef vr mp = M.alter fn vr mp
 where
   fn Nothing = if conservativeMode
                then error$"trackUses: addArrRef helper should not be used on var not in map: "++show vr
                else Just (Uses 0 1)
   fn (Just (Uses s a)) = Just (Uses s (a+1))

addScalarRef :: Var -> UseMap -> UseMap
addScalarRef vr mp =
  M.alter fn vr mp
 where
   fn Nothing = if conservativeMode
                then error$"trackUses: addScalarRef helper should not be used on var not in map: "++show vr
                else Just (Uses 1 0)
   fn (Just (Uses s a)) = Just (Uses (s+1) a)

-- Update a usemap with new usages found in an AExp.
doAE :: AExp -> UseMap -> UseMap
doAE ae mp =
  case ae of
    Use arr -> mp
    Use' arr -> mp
    Vr v                -> addArrRef v mp
    Map fn vr           -> addArrRef vr $ doFn1 fn mp
    ZipWith fn2 v1 v2   -> addArrRef v1 $ addArrRef v2 $ doFn2 fn2 mp
    Cond e1 v1 v2       -> addArrRef v1 $ addArrRef v2 $ doE e1 mp
    Generate e1 fn1     -> doE e1       $ doFn1 fn1 mp

    Fold fn e1 vr       -> addArrRef vr$ doE e1 $ doFn2 fn mp
    Fold1  fn vr        -> addArrRef vr$          doFn2 fn mp
    FoldSeg fn e1 v1 v2 -> addArrRef v1 $ addArrRef v2 $
                           doE e1       $ doFn2 fn mp 
    Fold1Seg  fn v1 v2  -> addArrRef v1 $ addArrRef v2 $ doFn2 fn mp
    Scanl  fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
    Scanl' fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
    Scanl1 fn2     vr   -> addArrRef vr $                doFn2 fn2 mp
    Scanr  fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
    Scanr' fn2 e1  vr   -> addArrRef vr $ doE e1       $ doFn2 fn2 mp
    Scanr1 fn2     vr   -> addArrRef vr $                doFn2 fn2 mp
    Permute fn2 v1 fn1 v2 -> addArrRef v1 $ addArrRef v2 $
                             doFn1 fn1    $ doFn2 fn2 mp
    Backpermute e1 fn1 vr -> addArrRef vr $ doE e1 $ doFn1 fn1 mp
    Stencil fn1 _b vr     -> addArrRef vr $ doFn1 fn1 mp
    Stencil2 fn2 _b1 v1 _b2 v2 -> addArrRef v1 $ addArrRef v2 $ doFn2 fn2 mp

    Reshape e1 vr       -> addArrRef vr $ doE e1 mp
    Replicate _slt e1 vr -> addArrRef vr $ doE e1 mp
    Index _slt vr e1     -> addArrRef vr $ doE e1 mp
    Unit _ -> error "trackUses: Unit is not part of the grammar accepted by this pass"

doFn1 :: Fun1 Exp -> UseMap -> UseMap
doFn1 (Lam1 _ exp) mp = doE exp mp 

doFn2 :: Fun2 Exp -> UseMap -> UseMap
doFn2 (Lam2 _ _ exp) mp = doE exp mp 

doE :: Exp -> UseMap -> UseMap
doE ex mp =
  case ex of
    EVr vr -> case M.lookup vr mp of
                Nothing -> if conservativeMode
                           then mp -- We don't track info for non-top-level bindings.
                           else addScalarRef vr mp
                Just _  -> addScalarRef vr mp
    ETuple els           -> doEs els mp
    EConst _             -> mp
    ELet (vr,ty,rhs) bod -> doE bod $ doE rhs mp 
    EPrimApp ty pr els   -> doEs els mp
    ECond e1 e2 e3       -> doE e1 $ doE e2 $ doE e3 mp
    EWhile (Lam1 _ bod1) (Lam1 _ bod2) e -> doE e $ doE bod1 $ doE bod2 mp 
    EIndexScalar avr ex  -> addScalarRef avr $ doE ex mp
    EShape avr           -> err ex 
    EShapeSize ex        -> err ex
    EIndex els           -> doEs els mp
    ETupProject _ _ ex   -> doE ex mp

err :: Show a => a -> b
err ex = error$"TrackUses.hs: this form should have been desugared by this point: "++show ex

doEs :: [Exp] -> UseMap -> UseMap
doEs els mp = L.foldl  (\mp ex -> doE ex mp) mp els
