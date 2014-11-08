{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This pass does the conversion to an abstract GPU program.  That
-- requires lifting out some scalar blocks and also inserting event identifiers.

module Data.Array.Accelerate.BackendKit.Phase3.ToGPUIR (convertToGPUIR) where

import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName,(#))
import           Data.Array.Accelerate.BackendKit.IRs.Metadata
import           Data.Array.Accelerate.BackendKit.IRs.CLike     as LL
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Control.Applicative   ((<$>))
import           Control.Monad.State.Strict (runState)
import qualified Data.Map                        as M
import qualified Data.Set                        as S
import           Text.PrettyPrint.GenericPretty (Out(doc))
-- import Debug.Trace (trace)
----------------------------------------------------------------------------------------------------


-- | This pass takes a SimpleAST IR which already follows a number of
--   conventions that make it directly convertable to the lower level
--   GPU IR, and it does the final conversion.
convertToGPUIR :: LLProg (FreeVars) -> G.GPUProg FreeVars
convertToGPUIR LLProg{progBinds,progResults,progType,uniqueCounter,sizeEnv} =
  G.GPUProg
  {
    G.progBinds      = binds, 
    G.progResults    = progResults,
    G.progType       = progType,
    G.uniqueCounter  = newCounter,
    G.lastwriteTable = concatMap fn binds,
    G.sizeEnv        = sizeEnv
  }
  where
    (binds,newCounter) = runState (doBinds sizeEnv M.empty progBinds) uniqueCounter
    -- In the initial translation the lastwriteTable is the identity:
    fn G.GPUProgBind{G.outarrs, G.evtid} =
      let (vs,_,_) = unzip3 outarrs in 
      map (\x -> (x,evtid)) vs

-- Default decoration for new scalar binds:
defaultDec :: FreeVars
defaultDec = FreeVars []

doBinds :: M.Map S.Var (S.Type, S.TrivialExp) -> M.Map S.Var G.EvtId ->
           [LLProgBind (FreeVars)] -> GensymM [G.GPUProgBind FreeVars]
doBinds _ _ [] = return []
doBinds sizeEnv evEnv (LLProgBind vartys (FreeVars fvs) toplvl : rest) = do
  newevt <- genEvt
  let rebind deps = G.GPUProgBind newevt deps (map liftBind vartys) (FreeVars fvs)
      evEnv' = foldl (\mp (v,_) -> M.insert v newevt mp) evEnv vartys
      -- Convert variable references to event ids:
      evs = map (\v -> case M.lookup v evEnv' of
                         Just x -> x
                         Nothing -> error$"ToGPUIR.hs: no event ID in map for: "
                                    ++show v++" map size "++show(M.size evEnv'))
--  trace ("TOGPUIR - extending evt env "++show vartys++" map size "++show(M.size evEnv')) $ return () 
  rst <- doBinds sizeEnv evEnv' rest

  let -- shared code for cases below:
      -- Create a new progbind that lifts out a scalarblock:
    {--
      liftSB :: ScalarBlock -> GensymM (G.GPUProgBind FreeVars, [S.Var])
      liftSB sb = do
         let (ScalarBlock bnds rets _) = sb
             retTys = map snd $ filter (\ (v,_) -> elem v rets) bnds
         newVs <- sequence (replicate (length rets) genUnique)
         evt2 <- genEvt
         let sbBnd = G.GPUProgBind
                     { G.evtid   = evt2,
                       G.evtdeps = evs$ S.toList $ LL.scalarBlockFreeVars sb,
                       G.outarrs = [(v, topLvlAddrSpc t, t) | t <- retTys | v <- newVs ], 
                       G.decor   = defaultDec,
                       G.op      = G.ScalarCode (doSB sb) }
         return (sbBnd, newVs)
      --}
      -- Lift out an SB AND repack it as a new SB.
      -- goSB sb = do (pb,vrs) <- liftSB sb
      --              sb' <- G.expsToBlock (zip (map G.EVr vrs)
      --                                        (error "need vr types..."))
      --              return (pb,sb')
  
      -- May have to handle scalar blocks and thus return new ProgBinds:
      doVariant ::                              ReduceVariant Fun ScalarBlock ->
                   GensymM ([G.GPUProgBind FreeVars], ReduceVariant G.Fun G.ScalarBlock)
      -- TODO: progbind return val is obselete:
      doVariant rvar =
        case rvar of
          Fold sb -> do let sb' = doSB sb -- (pb,sb') <- goSB sb
                        return ([], Fold sb')
          FoldSeg sb gen2  -> do let sb' = doSB sb -- (pb,sb') <- goSB sb
                                 return ([], FoldSeg sb' (doMGen gen2))
          Scan dir sb      -> do let sb' = doSB sb -- (pb,sb') <- goSB sb
                                 return ([], Scan dir sb')
          Scan1 dir        -> return ([], Scan1 dir) -- nothing to do? 
          Permute lam mgen -> return ([], Permute (doLam lam) (doMGen mgen))          
  
  case toplvl of
    Use arr       -> return$ rebind [] (G.Use arr)                       : rst
    Use' v arr    -> return$ rebind [] (G.Use' v arr)                    : rst
    Cond e v1 v2  -> return$ rebind (evs [v1,v2]) (G.Cond (doE e) v1 v2) : rst
    ScalarCode sb -> return$ rebind (evs fvs) (G.ScalarCode (doSB sb))   : rst

-- FINISH ME
    GenManifest gen -> do
      -- (sbBnd, els) <- liftSB sb -- Easier now that it's not a full ScalarBlock
      let newBnd = rebind (evs fvs) $
                    G.GenManifest (doGen gen)
      -- return (sbBnd : newBnd : rst)
      return (newBnd : rst)

    GenReduce { reducer, generator, variant, stride } -> do
      let gen' = doMGen generator
      (sbs, var') <- doVariant variant
      let stride' = case stride of
                      StrideAll     -> StrideAll
                      StrideConst e -> StrideConst$ doE e
      let newBnd = 
           rebind (evs fvs) $
            G.GenReduce { G.reducer   = doLam reducer,
                          G.generator = gen',
                          G.variant   = var',
                          G.stride    = stride'
                        }
      return (sbs ++ newBnd : rst)

    _ -> error$"ToGPUIR.hs: Incomplete, must handle top level form:\n "++show(doc toplvl)

 where
   (_nm,_ty) = case vartys of -- Touch this and you make the one-output-array assumption!
     [x] -> x 
     _oth -> error$"ConvertGPUIR.hs: expected one output from op:\n  "++show toplvl

   genEvt = genUniqueWith "evt"

   doMGen mgen = case mgen of
                   Manifest vs     -> Manifest vs
                   NonManifest gen -> NonManifest $ doGen gen
   doGen (Gen tr lam) = G.Gen tr (doLam lam)
   doLam (Lam args bod) = G.Lam (map liftBind args) (doSB bod)


doSB :: ScalarBlock -> G.ScalarBlock
doSB (ScalarBlock ls rets stmts) =
  G.ScalarBlock (map liftBind ls) rets (doStmts stmts)

-- | Stick in a default memory location based on the type:
liftBind :: (S.Var, S.Type) -> (S.Var, G.MemLocation, S.Type)
liftBind (v,t) = (v, typeToAddrSpc t, t)

-- Top level bindings are all GLOBAL presently:
topLvlAddrSpc :: S.Type -> G.MemLocation
topLvlAddrSpc = typeToAddrSpc

typeToAddrSpc :: S.Type -> G.MemLocation
typeToAddrSpc (S.TArray _ _) = G.Global
typeToAddrSpc _              = G.Default

doStmt :: Stmt -> G.Stmt
doStmt st =
  case st of
    SCond e l1 l2 -> G.SCond (doE e) (doStmts l1) (doStmts l2)
    SSet vr ex    -> G.SSet vr (doE ex)
    
    SWhile v (Lam vs1 (ScalarBlock vl1 r1 stms1)) 
             (Lam vs2 (ScalarBlock vl2 r2 stms2))
                      (ScalarBlock vl3 r3 stms3) -> 
          G.SWhile v (G.Lam (map liftBind vs1)  
                          (G.ScalarBlock (map liftBind vl1) r1 (doStmts stms1)))
                     (G.Lam (map liftBind vs2)
                          (G.ScalarBlock (map liftBind vl2) r2 (doStmts stms2)))
                     (G.ScalarBlock (map liftBind vl3) r3 (doStmts stms3))

doStmts :: [Stmt] -> [G.Stmt]
doStmts = map doStmt


--CLike to GPUIR 
doE :: Exp -> G.Exp
doE ex =
  case ex of
    EConst c -> G.EConst c
    EVr v    -> G.EVr v
    EPrimApp t p ls -> G.EPrimApp t p (map doE ls)
    ECond a b c     -> G.ECond (doE a) (doE b) (doE c)
-- Going with G.Default 
--    EWhile (Lam [(v1,t1)] bod1) (Lam [(v2,t2)] bod2) e -> G.EWhile (G.Lam [(v1, G.Default, t1)] (doE bod1) )
--                                                                   (G.Lam [(v2, G.Default, t2)] (doE bod2) ) 
--                                                                   (doE e) 
    EIndexScalar v e i | i == 0    -> G.EIndexScalar v (doE e)
                       | otherwise -> error$"ConvertLLIR.hs/doE: only handles EIndexScalar without tuple dereference index: "++show i
 
