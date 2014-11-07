{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

module Data.Array.Accelerate.BackendKit.Phase3.FuseGenReduce (fuseGenReduce) where

import           Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
-- import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName)
import           Data.Array.Accelerate.BackendKit.IRs.Metadata
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.Utils.Helpers(maybtrace)
import qualified Data.Map                        as M
import           Data.Maybe                      (fromJust,isJust,catMaybes) 
import qualified Data.Set                        as S
-- import           Text.PrettyPrint.GenericPretty (Out(doc))
--------------------------------------------------------------------------------

-- | A pass to inline [manifest] Generate's that are only used in one reduce, into
-- that reduction.
fuseGenReduce :: G.GPUProg FreeVars -> G.GPUProg FreeVars
fuseGenReduce prog@GPUProg{progBinds, uniqueCounter, sizeEnv} =
  prog {
    progBinds = filter (not . isInlined) binds
  }
  where
    (binds,inlined) = doBinds potentialInlines progBinds
    isInlined GPUProgBind{outarrs,op=GenManifest{}} = and [ S.member v inlined | (v,_,_) <- outarrs]
    isInlined                    _ = False

    potentialInlines =
      M.filter isGenManifest $ 
      M.mapWithKey (\ vr _ -> fromJust (G.lookupProgBind vr progBinds))
      potentialInlineVrs

    isGenManifest (GPUProgBind{op=GenManifest{}}) = True
    isGenManifest _ = False

    -- Here we determine which GenManifest ops are single-use (this is a degenerate
    -- form of TrackUses):
    potentialInlineVrs =
      -- Anything that (1) is only an input to GenReduce once, and (2) does not occur
      -- in kernel free vars, is potentially inlinable.
      M.filterWithKey (\vr cnt -> cnt == 1 && not (S.member vr inKernUses)) reduceUses
      
    reduceUses = countMap $ concatMap fn progBinds
    -- BEWARE - if OTHER consumers than GenReduce are added, those need to be
    -- accounted for here as well:
    fn GPUProgBind { op=GenReduce{generator=Manifest vrs} } = vrs
    fn _ = []
    
    inKernUses = S.fromList $ 
      concatMap (\ GPUProgBind { decor=FreeVars ls } -> ls) progBinds

countMap :: Ord a => [a] -> M.Map a Int
countMap ls = M.fromListWith (+) (map (,1) ls)

-- Takes a list of possible-inlines, returns new bindings, plus a list of those
-- actually-inlined.
doBinds :: M.Map S.Var (GPUProgBind FreeVars) ->
           [GPUProgBind FreeVars] -> ([GPUProgBind FreeVars], S.Set S.Var)
doBinds inlines binds = loop [] [] binds 
  where
    loop bacc vacc [] = (reverse bacc, S.fromList vacc)
    loop bacc vacc (pb@GPUProgBind { op, decor=FreeVars fvs } : rest) = do  
      let skip  = loop (pb:bacc) vacc rest
      case op of
         Use  _        -> skip
         Use' _        -> skip
         -- TODO: We have the option here to turn array level conditionals into
         -- scalar conditionals:
         Cond _ _ _    -> skip
         ScalarCode _  -> skip
         GenManifest _ -> skip
         GenReduce {generator} ->
           let Manifest vrs = generator
               bods = map (`M.lookup` inlines) vrs in
           -- The separate components of the input *should* all come from the same
           -- place, but we make sure here:
           case S.toList$ S.fromList$ catMaybes bods of
             [] -> skip
             [one] ->
                case one of
                  GPUProgBind { outarrs, op=GenManifest theGEN, decor=FreeVars fvs2 } ->                    
                    let -- This part is easy, we just plug it in:
                        pb' = pb{ op= op{ generator= NonManifest theGEN},
                                  -- Sticky issue, do free vars include the generator AND the reducer?
                                  -- ANSWER: For now, *YES*.    
                                  decor= FreeVars (fvs++fvs2) } in
                    if all isJust bods
                    then maybtrace ("!! VICTORY - fusing GenManifest into Reduce: "++show outarrs)$  
                         loop (pb':bacc) (vrs++vacc) rest
                    else skip
                  _ -> error$"FuseGenReduce.hs: unexpected op upstream from GenReduce: "++show one
             ls -> error$"FuseGenReduce.hs: cannot presently handle inlining more than one GenManifest into GenReduce: "++show ls
               
         NewArray _    -> error$"FuseGenReduce.hs: not expecting NewArray yet: "++show op
         Kernel {}     -> error$"FuseGenReduce.hs: not expecting Kernel yet: "++show op
