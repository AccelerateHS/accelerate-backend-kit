{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

module Data.Array.Accelerate.BackendKit.Phase3.FuseGenReduce (fuseGenReduce) where

import           Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
-- import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName)
import           Data.Array.Accelerate.BackendKit.IRs.Metadata
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
-- import           Control.Applicative   ((<$>))
-- import           Control.Monad.State.Strict (runState)
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
    isInlined GPUProgBind{outarrs} = and [ S.member v inlined | (v,_,_) <- outarrs]
    isInlined                    _ = False

    potentialInlines =
      M.mapWithKey (\ vr _ -> 
                     case G.lookupProgBind vr progBinds of
                       Just (GPUProgBind{op=GenManifest gen}) -> gen)
      potentialInlineVrs

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
doBinds :: M.Map S.Var (Generator (Fun ScalarBlock)) ->
           [GPUProgBind a] -> ([GPUProgBind a], S.Set S.Var)
doBinds inlines binds = loop [] [] binds 
  where
    loop bacc vacc [] = (reverse bacc, S.fromList vacc)
    loop bacc vacc (pb@GPUProgBind { op } : rest) = do  
      let err = error "FINISHME"
          skip  = loop (pb:bacc) vacc rest
      case op of
         Use  _        -> skip         
         -- TODO: We have the option here to turn array level conditionals into
         -- scalar conditionals:
         Cond _ _ _    -> skip
         ScalarCode _  -> skip
         GenManifest _ -> skip
         GenReduce {generator,reducer} ->
           let Manifest vrs = generator
               bods = map (`M.lookup` inlines) vrs in
           -- The separate components of the input *should* all come from the same
           -- place, but we make sure here:
            if all isJust bods
            then let pb' = pb{op= op{reducer= doInline (M.fromList$ zip vrs $ catMaybes bods) reducer }}
                 in loop (pb':bacc) (vrs++vacc) rest
            else skip

         NewArray _    -> error$"FuseGenReduce.hs: not expecting NewArray yet: "++show op
         Kernel {}     -> error$"FuseGenReduce.hs: not expecting Kernel yet: "++show op
         
doInline :: M.Map S.Var (Generator (Fun ScalarBlock)) -> Fun ScalarBlock -> Fun ScalarBlock
doInline mp (Lam vs (ScalarBlock locals res stmts)) =
  Lam vs $ ScalarBlock locals res (map doStmt stmts)
 where
   
  doStmt st =
    error "finishme"

-- data Stmt =   
--     SCond Exp [Stmt] [Stmt]
--   | SSet    Var Exp             -- v = exp
--   | SArrSet Var Exp Exp         -- arr[exp] = exp
--   | SFor { forvar :: Var,
--            forinit :: Exp,
--            fortest :: Exp,
--            forincr :: Exp,
--            forbody :: [Stmt]
--            }                    -- for (init,test,incr) { body }
--   | SNoOp                       -- no operation
--   | SSynchronizeThreads

--     -- Comments to be emitted to generated code:
--   | SComment String
--  deriving (Read,Show,Eq,Ord,Generic)

-- data MemLocation = Default | Global | Local | Private | Constant 
--  deriving (Read,Show,Eq,Ord,Generic)

-- data Exp = 
--     EConst SA.Const           
--   | EVr Var
--   | EGetLocalID  Int            -- The Int specifies dimension: 0,1,2
--   | EGetGlobalID Int 
--   | EPrimApp Type SA.Prim [Exp]
--   | ECond Exp Exp Exp        
--   | EIndexScalar Var Exp        -- Reads a tuple from an array, and does index-from-right into that tuple.
--   | EUnInitArray Type Int       -- This is ONLY here as a special OpenCL convention.  "Local" memory
--                                 -- arrays are passed into the kernel as NULL ptrs WITH sizes (here in #elements).

-- data GPUProgBind d = GPUProgBind {
--       evtid   :: EvtId,                    -- ^ EventID for this operator's execution.      
--       evtdeps :: [EvtId],                  -- ^ Dependencies for this operator.      
--       outarrs :: [(Var,MemLocation,Type)], -- ^ Outputs of this operator.
--       decor   :: d,                        -- ^ Parameterizable decoration
--       op      :: TopLvlForm                -- ^ The operator itself.
--     }
