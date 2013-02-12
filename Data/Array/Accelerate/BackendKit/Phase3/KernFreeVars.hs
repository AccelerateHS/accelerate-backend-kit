{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module defines a compiler pass for counting variable uses.

module Data.Array.Accelerate.BackendKit.Phase3.KernFreeVars (kernFreeVars) where

-- import Data.Array.Accelerate.SimpleAST      as T
-- import qualified ClassSupport.B629.TypeDefs as LL
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SA
import           Data.Array.Accelerate.BackendKit.IRs.CLike     as LL
import           Data.Array.Accelerate.BackendKit.IRs.Metadata (FreeVars(FreeVars))
import           Data.List as L
import           Data.Set  as S

-- | A compiler pass that adds metadata only.  It counts the uses of
--   all array and scalar variables.  
kernFreeVars :: LLProg () -> LLProg (FreeVars)
kernFreeVars prog@LLProg{progBinds} =
  prog{ progBinds= L.map doBind progBinds}

doBind :: LLProgBind () -> LLProgBind (FreeVars)
-- This pass measures KERNEL free vars, these scalar expressions don't count:
doBind (LLProgBind vrs () op) = LLProgBind vrs (FreeVars (S.toList (doAE op))) op

-- | Free variables for ONLY the kernel of an AE:
--
-- FIXME: This is screwed up by multi-kernel forms like Permute.
doAE :: LL.TopLvlForm -> S.Set SA.Var
doAE ae =
  case ae of
    LL.Use _            -> S.empty
    LL.Cond _ _  _      -> S.empty
    LL.ScalarCode blk   -> doBlk blk
    -- The free vars for a generate binding refer to the body of the
    -- Generate, NOT the size expression.
    LL.GenManifest gen  -> doGenerator gen

    -- FIXME: Need a better system here.
    -- We union the freevars in BOTH the reducer and the generator:
    LL.GenReduce { reducer= Lam binds1 bod1, generator } ->

      -- TEMPORARY: At this pass we currently assume that all GenReduce args are MANIFEST:
      case generator of
        Manifest inVs  -> 
         let s1 = doBlk bod1 in
   --          s2 = doBlk bod2 in
         S.difference s1 -- (S.union s1 s2)
          (S.fromList$ L.map fst binds1) -- ++ L.map fst binds2)
      
    -- This one isn't a good fit... it has TWO lambdas:  
    -- Permute (Lam2 (x,_) (y,_) bod1) _ (Lam1 (v,_) bod2) _ 


doBlk :: ScalarBlock -> Set SA.Var
doBlk  = LL.scalarBlockFreeVars

doGenerator :: Generator (Fun ScalarBlock) -> Set SA.Var
doGenerator (Gen _ (Lam args bod)) = 
      S.difference (doBlk bod)
                   (S.fromList$ L.map fst args)
