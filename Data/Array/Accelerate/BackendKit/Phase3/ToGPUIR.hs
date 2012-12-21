{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This pass does the conversion to an abstract GPU program.  That
-- requires lifting out some scalar blocks and also inserting event identifiers.

module Data.Array.Accelerate.BackendKit.Phase3.ToGPUIR (convertToGPUIR) where

import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName)
import           Data.Array.Accelerate.BackendKit.IRs.Metadata
import           Data.Array.Accelerate.BackendKit.IRs.CLike     as LL
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Control.Applicative   ((<$>))
import           Control.Monad.State.Strict (runState)
import qualified Data.Map                        as M
import qualified Data.Set                        as S

----------------------------------------------------------------------------------------------------


-- | This pass takes a SimpleAST IR which already follows a number of
--   conventions that make it directly convertable to the lower level
--   GPU IR, and it does the final conversion.
convertToGPUIR :: LLProg (ArraySizeEstimate,FreeVars) -> G.GPUProg (ArraySizeEstimate,FreeVars)
convertToGPUIR LLProg{progBinds,progResults,progType,uniqueCounter} =
  G.GPUProg
  {
    G.progBinds     = binds, 
    G.progResults   = progResults,
    G.progType      = progType,
    G.uniqueCounter = newCounter,
    G.lastwriteTable   = concatMap fn binds
  }
  where
    (binds,newCounter) = runState (doBinds M.empty progBinds) uniqueCounter
    -- In the initial translation the lastwriteTable is the identity:
    fn G.GPUProgBind{G.outarrs, G.evtid} =
      let (vs,_,_) = unzip3 outarrs in 
      map (\x -> (x,evtid)) vs

-- Default decoration for new scalar binds:
defaultDec :: (ArraySizeEstimate, FreeVars)
defaultDec = (UnknownSize, FreeVars [])

-- This procedure keeps around a "size map" from array values names to
-- their number of elements.
doBinds :: M.Map S.Var G.EvtId ->
           [LLProgBind (ArraySizeEstimate,FreeVars)] -> GensymM [G.GPUProgBind (ArraySizeEstimate,FreeVars)]
doBinds _ [] = return []
doBinds evEnv (LLProgBind vartys dec@(_,FreeVars fvs) toplvl : rest) = do
  newevt <- genEvt
  let rebind deps = G.GPUProgBind newevt deps (map liftBind vartys) dec
      evEnv' = foldl (\mp (v,_) -> M.insert v newevt mp) evEnv vartys
  rst <- doBinds evEnv' rest

  let -- shared code for cases below:
      liftSB sb cont = do
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
         otherBnd <- cont (map G.EVr newVs)
         return (sbBnd : otherBnd : rst)      

  case toplvl of
    Use arr       -> return$ rebind [] (G.Use arr)                       : rst
    Cond e v1 v2  -> return$ rebind (evs [v1,v2]) (G.Cond (doE e) v1 v2) : rst
    ScalarCode sb -> return$ rebind (evs fvs) (G.ScalarCode (doSB sb))   : rst

    Generate sb (Lam args bod) ->
      liftSB sb $ \ els -> return $ 
        rebind (evs fvs) $ G.Generate els (G.Lam (map liftBind args) (doSB bod))
    
    Fold (Lam args bod) sb inV seg  -> 
      liftSB sb $ \ els -> return $
        let seg' = case seg of
--                     Nothing -> G.ConstantStride (error "Need more information on fold stride...")
--                    Nothing -> G.ConstantStride (G.EVr (strideName nm))
                    -- TEMP: For the moment we are NOT using the stride component:
                    Nothing -> G.ConstantStride (G.EConst (S.I 0))
                    Just v  -> G.VariableStride v
        in rebind (evs$ inV:fvs) $ 
           G.Fold (G.Lam (map liftBind args) (doSB bod))
                  els inV seg'

  -- Not supporting Scan yet:
  -- | Scan (Fun ScalarBlock) Direction ScalarBlock Var  
 where
   (nm,ty) = case vartys of -- Touch this and you make the one-output-array assumption!
              [x] -> x 
              oth -> error$"ConvertGPUIR.hs: expected one output from op:\n  "++show toplvl

   -- Convert variable references to event ids:
   evs = map (evEnv M.!)
   genEvt = genUniqueWith "evt"


doSB :: ScalarBlock -> G.ScalarBlock
doSB (ScalarBlock ls rets stmts) =
  G.ScalarBlock (map liftBind ls) rets (doStmts stmts)

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

doStmts :: [Stmt] -> [G.Stmt]
doStmts = map doStmt

doE :: Exp -> G.Exp
doE ex =
  case ex of
    EConst c -> G.EConst c
    EVr v    -> G.EVr v
    EPrimApp t p ls -> G.EPrimApp t p (map doE ls)
    ECond a b c     -> G.ECond (doE a) (doE b) (doE c)
    EIndexScalar v e i | i == 0    -> G.EIndexScalar v (doE e)
                       | otherwise -> error$"ConvertLLIR.hs/doE: only handles EIndexScalar without tuple dereference index: "++show i
 
