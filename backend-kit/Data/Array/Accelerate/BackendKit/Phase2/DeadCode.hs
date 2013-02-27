{-# LANGUAGE NamedFieldPuns #-}

-- | A pass to eliminate any top-level array and scalar variables whose use counts
-- have fallen to zero.

module Data.Array.Accelerate.BackendKit.Phase2.DeadCode (deadCode) where 

import Data.List as L
import Data.Map  as M
import Data.Set  as S
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.IRs.Metadata (Uses(Uses))
import Data.Array.Accelerate.BackendKit.CompilerUtils (maybtrace, isShapeName, isSizeName)
import qualified Data.Array.Accelerate.BackendKit.Phase2.TrackUses as TU

-- | Dead code elimination.
deadCode :: Prog (a,Uses) -> Prog a
deadCode prog@Prog{progBinds} = fmap fst$
  prog{ progBinds= L.filter ((`S.member` survivors) . getName) progBinds }
 where
  survivors = M.keysSet $ loop M.empty progBinds
  getName (ProgBind v _ _ _) = v

-- | We process an incoming list of ProgBinds, and each one we remove
--  can trigger further removals from the already accumulated bindings.
--  This returns a map of *surving* variables to their #uses.
loop :: Map Var Int -> [ProgBind (a,Uses)] -> Map Var Int  
loop mp [] = mp

loop mp (ProgBind v _ (_,Uses 0 0) _ : rest)
  | isSizeName v || isShapeName v =
    maybtrace (".. deadArrays refusing to eliminate size/shape var: "++show v) $
   loop (M.insert v 0 mp) rest

loop mp (ProgBind v _ (_,Uses 0 0) rhs : rest) =
    maybtrace ("!! Victory: deadArrays, start an unraveling by eliminating: "++show v)  
    loop mp' rest
  where 
    -- Here we are removing the binding in question, decrement other
    -- bindings appropriately, remove if necessary:
    mp' = L.foldl (\ acc (fv,Uses su au) ->
                   let (_,x) = M.updateLookupWithKey
                               (\ _k cnt ->
                                 case cnt - su - au of
                                   0 ->
                                        maybtrace ("!! Victory: deadArrays, continuing in that thread: "++show v)
                                        Nothing -- Delete it!
                                   n -> Just n)
                                fv acc
                   in x)
               mp (M.toList$ theseUses)
    theseUses = case rhs of
                  Right ae -> TU.doAE ae M.empty
                  Left  ex -> TU.doE  ex M.empty

-- Otherwise the binding is still "live" and sticks around, at least for now:
loop mp (ProgBind v _ (_,Uses su au) _ : rest) =
   loop (M.insert v (su+au) mp) rest    
