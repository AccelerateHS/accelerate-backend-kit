{-# LANGUAGE NamedFieldPuns #-}

-- | This module defines a compiler pass for removing the `Unit` construct.

module Data.Array.Accelerate.BackendKit.Phase2.FuseMaps (fuseMaps) where 

import Data.Array.Accelerate.BackendKit.IRs.Metadata (Uses(..), ArraySizeEstimate(..))

import Test.Framework                    (defaultMain)
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as T
import Data.Array.Accelerate.BackendKit.CompilerUtils (maybtrace)
import Data.List as L
import Data.Map  as M
import Debug.Trace (trace)
import Text.PrettyPrint.GenericPretty    (Out,doc)

-- Victory messages are ALWAYS ON for now:
mtrace = maybtrace

fuseMaps :: Prog (ArraySizeEstimate,Uses) -> Prog (ArraySizeEstimate,Uses)
fuseMaps prog@Prog{progBinds} =
  prog { progBinds= doBinds [] M.empty progBinds}
  -- TODO: Remove dead entries from the typeEnv.

fuseLam1s :: Fun1 Exp -> Fun1 Exp -> Fun1 Exp
fuseLam1s (Lam1 (v1,ty1) bod1) (Lam1 (v2,ty2) bod2) =
  (Lam1 (v2,ty2)$
   ELet (v1,ty1,bod2) bod1)

fuseLam12 :: Fun1 Exp -> Fun2 Exp -> Fun2 Exp
fuseLam12 (Lam1 (v1,ty1) bod1) (Lam2 arg2 arg3 bod2) = 
  Lam2 arg2 arg3 $ 
  ELet (v1,ty1,bod2) bod1

type PB = ProgBind (ArraySizeEstimate,Uses)

-- This function processes a list of topologically sorted (def before use) bindings.
--
-- It keeps two accumulators just to track the post-FUSION bindings in
-- two different kinds of data structures.
doBinds :: [PB] -> (M.Map Var PB) -> [PB] -> [PB]
doBinds newBinds newBindsM [] = reverse newBinds
-- No fusion to be done on scalar bindings:
doBinds newBinds newBindsM (pb@(ProgBind _ _ _ (Left _)) : rest) = doBinds (pb : newBinds) newBindsM rest

-- TODO/FIXME: rather than deleting from the newBinds list (which can
-- make this pass quadratic), it is better to do a single pruning pass
-- at the end, checking newBinds' elements for membershi pin newBindsM
-- (which is n*log(n)).
doBinds newBinds newBindsM (thisOne@(ProgBind vrOut ty decor (Right ae)) : rest) =
  -- Perform fusion if possible:
  case ae of
    -- CASE 1: A Map applied to something else could be pushed into the something else:
    --------------------------------------------------------------------------------
    Map fnA vrIn ->
      let upstream  = newBindsM M.! vrIn          
          fuse      = fuseIt upstream . rebuild
      in case upstream of
        -- The case we care about is a SINGLE-USE upstream Map:
        ProgBind _ _ (_,Uses 0 1) (Right (Map fnB vrB)) ->
          fuse$  Map (fuseLam1s fnA fnB) vrB

        -- Likewise a single-use upstream Generate:
        ProgBind _ _ (_,Uses 0 1) (Right (Generate ex fnB)) ->
          fuse$  Generate ex (fuseLam1s fnA fnB)

        -- Ditto for ZipWith:
        ProgBind _ _ (_,Uses 0 1) (Right (ZipWith fnB vr1 vr2)) ->
          fuse$  ZipWith (fuseLam12 fnA fnB) vr1 vr2

        -- Tenderizing!  This isn't fusion, but may enable fusion.  We
        -- push Map through Replicate to the other side and then
        -- continue optimization.
        ProgBind rpV _ (rpSz,Uses 0 1) (Right (Replicate sty ex rpUpVr)) ->
          mtrace ("!! victory -- Push Map "++show vrOut ++" through Replicate "++show rpV)$
          let upupstream = newBindsM M.! rpUpVr 
              ProgBind _ (TArray origDim _) (origSz,_) _ = upupstream 
              TArray _ elty = ty in
          -- We take the Replicate OUT of the newBinds, we swap the
          -- order, and we continue processing:          
          doBinds (L.delete upstream newBinds) (M.delete rpV newBindsM)
                  -- This is tricky, the type of the Map output stays
                  -- the same.  The type of the replicate changes.
                  -- The #uses of the Map becomes the #uses of the
                  -- Replicate.  (The sizes are the same anyway.)
                  -- Finally, the inputs/outputs are rewired.
                  (ProgBind rpV (TArray origDim elty) (origSz,Uses 0 1) (Right (Map fnA rpUpVr)) :
                   ProgBind vrOut ty  decor          (Right (Replicate sty ex rpV)) : 
                   rest)

        _ -> keepGoing thisOne -- ANYTHING else won't fuse.

    --------------------------------------------------------------------------------
    -- CASE 2: A ZipWith (i.e. Map2) where one or the other branch can be sucked in.
    --------------------------------------------------------------------------------

    -- First handle an unusual case:
    ZipWith (Lam2 (a1,t1) (a2,t2) bod) v1 v2 | v1 == v2 ->
      -- Here we also need to rewrite the upstream to decrement the use count:
      let upstream@(ProgBind upV _ (_,Uses _ au) _) = newBindsM M.! v1
          newUp = fmap (\ (d, Uses su au) -> (d, Uses su (au - 1))) upstream
      in
      mtrace ("!! VICTORY - rewriting silly ZipWith over identical inputs as a Map... (decrementing use count to "++
              show (au-1)++")\n   "++ show(doc ae))$
      -- FIXME: Need to get rid of this (quadratic) usage of newBinds:
      doBinds (newUp : L.delete upstream newBinds)
              (M.insert upV newUp newBindsM)
              (rebuild (Map (Lam1 (a1,t1) (ELet (a2,t2,EVr a1) bod)) v1) : rest)

    ZipWith (Lam2 argA1@(a1,t1) argA2 bodA) vrA1 vrA2 ->
      case (newBindsM M.! vrA1,
            newBindsM M.! vrA2) of
        -- IF there is a hit on the RIGHT we flip to deal with it:
        (_,ProgBind upV _ (_,Uses 0 1) (Right mp@(Map _ _))) ->
           mtrace ("!! victory is CLOSE -- Fusable input on right of zipwith, FLIPPING.")$
           doBinds newBinds newBindsM (rebuild (ZipWith (Lam2 argA2 argA1 bodA) vrA2 vrA1) : rest)

        -- A hit on the left we process and flip [back].
        (upstream@(ProgBind upV _ (_,Uses 0 1) (Right (Map (Lam1 argB bodB) vrB))), _) ->
          -- Here we perform a little trick to avoid code duplication.
          -- Flip the arg order and try again:
          let lam = Lam2 argA2 argB $ ELet (a1,t1,bodB) bodA in
          mtrace ("!! VICTORY -- accomplished zipwith fusion, eliminated:\n   "++show (doc upstream))$ 
          doBinds (L.delete upstream newBinds) (M.delete upV newBindsM)
                  (rebuild (ZipWith lam vrA2 vrB) : rest)
        _ -> keepGoing thisOne 

  
    -----------------
    -- TODO: If both branches of a zipwith are generates they can be
    -- COMBINED into just one generate (if shapes are equal).

    -----------------          
    -- TODO: A single-use generate can be inlined into the ZipWith
    -- (transforming it to a Map) WITHOUT increasing total work.    
    -- BUT, this would require some ability to refer to the "current
    -- location" with a map.... so we can't do it for now.

    -----------------
    -- TODO: Handle replicated constants as inputs to zipwith.  This
    -- will come out as Replicated Generate's which is a bit tricky.
    -- A more general optimization is to fuse replicate into generate
    -- IF the work-estimate is low (i.e. a constant!).

    --------------------------------------------------------------------------------
    -- CASE 3: Fuse Backpermute's
    --------------------------------------------------------------------------------
    -- TODO: Implement me

    _ -> keepGoing thisOne
  where
    rebuild x = ProgBind vrOut ty decor (Right x)
    keepGoing newbind = doBinds (newbind : newBinds) (M.insert vrOut newbind newBindsM) rest

    -- When doing fusion we REMOVE the old binding that has been fused.
    fuseIt upstream@(ProgBind upname _ _ _) newbind = 
      mtrace ("!! VICTORY -- accomplished fusion into Map, eliminated:\n   "++show (doc upstream))$ 
      doBinds (newbind : L.delete upstream newBinds)
              (M.insert vrOut newbind (M.delete upname newBindsM))
              rest
--    addNGo newbind = newbind : doBinds (M.insert vrOut newbind newBindsM) rest


