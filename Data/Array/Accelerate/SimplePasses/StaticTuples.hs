{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

--------------------------------------------------------------------------------
-- | Compiler pass to remove dynamic cons/head/tail on indices.
--------------------------------------------------------------------------------

-- UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED UNFINISHED 

module Data.Array.Accelerate.SimplePasses.StaticTuples
       (         
         -- staticTuples -- Unfinished
       )
       where 

-- standard libraries
import Control.Monad
import Control.Applicative ((<$>),(<*>))
import Prelude                                     hiding (sum)
import Control.Monad.State.Strict (State, evalState, runState, get, put, modify)
import Data.Map as M
import Data.List as L
import Text.PrettyPrint.GenericPretty (Out(doc), Generic)
import Data.Array.Accelerate.SimpleAST   as S
import Data.Array.Accelerate.SimplePasses.IRTypes as T

import Debug.Trace(trace)
tracePrint s x = trace (s ++ show x) x


-- | This removes dynamic cons/head/tail on indices.  Indices are
--   plain tuples after this pass.
staticTuples :: TAExp -> TAExp
staticTuples ae = aexp M.empty ae
 where
--   aexp :: M.Map Var Int -> AExp -> [Builder]
   
   -- Trace the spine of lets.  We allow array tuples only at the very end:
   prog tenv aex = 
     case aex of 
       -- Lift out Let's as we encounter them:
       T.Let rt1 (v1,t1, T.Let rt2 (v2,t2,rhs) bod1) bod2 -> 
         -- NOTE: rt1 and rt2 should be equivalent:
         prog tenv $ T.Let rt1 (v2,t2,rhs) $
                     T.Let rt2 (v1,t1,bod1) bod2
       oth -> aexp tenv oth

   aexp tenv aex = 
     case aex of 
       
       -- Here we convert Apply to Let:
       T.Apply rty fn ae -> 
         T.Let rty (v,ty, aexp tenv' abod) (aexp tenv ae)
         where tenv' = M.insert v ty tenv         
               S.Lam1 (v,ty) abod = fn 
       
       -- TODO: Can we get rid of array tupling entirely?
       T.ArrayTuple rty aes -> T.ArrayTuple rty $ L.map (aexp tenv) aes       

       -- T.Let (vr,ty, T.ArrayTuple rhss) bod -> error "T.Let FINISHME"
         -- T.Let (vr,ty,loop rhs) (loop bod)
         -- where loop = aexp (M.insert vr ty tenv)

       -- The rest is BOILERPLATE; could scrap if we so chose:
       -------------------------------------------------------
       T.Vr rt vr -> T.Vr rt vr
       T.Let rt (vr,ty,rhs) bod -> T.Let rt (vr,ty,aexp tenv' rhs) (aexp tenv bod)
          where tenv' = M.insert vr ty tenv
       T.Unit rt ex -> T.Unit rt (exp tenv ex)
            
       T.Generate aty ex fn -> T.Generate aty (exp tenv ex) (lam1 tenv fn)
       T.ZipWith rt fn ae1 ae2 -> T.ZipWith rt (lam2 tenv fn) (aexp tenv ae1) (aexp tenv ae2)
       T.Map     rt fn ae      -> T.Map rt (lam1 tenv fn) (aexp tenv ae)

       T.TupleRefFromRight rt ind ae -> T.TupleRefFromRight rt ind (aexp tenv ae)

       T.Cond rt ex ae1 ae2 -> T.Cond rt (exp tenv ex) (aexp tenv ae1) (aexp tenv ae2)
       T.Use ty arr -> T.Use ty arr
 
       T.Replicate aty slice ex ae -> T.Replicate aty slice (exp tenv ex) (aexp tenv ae)
       T.Index     rt slc ae ex -> T.Index rt slc (aexp tenv ae) (exp tenv ex)
              
       T.Fold  rt fn einit ae         -> T.Fold  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Fold1 rt fn       ae         -> T.Fold1 rt (lam2 tenv fn) (aexp tenv ae)
       T.FoldSeg rt fn einit ae aeseg -> T.FoldSeg  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae) (aexp tenv aeseg)
       T.Fold1Seg rt fn      ae aeseg -> T.Fold1Seg rt (lam2 tenv fn) (aexp tenv ae) (aexp tenv aeseg)
       T.Scanl    rt fn einit ae      -> T.Scanl  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanl'   rt fn einit ae      -> T.Scanl' rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanl1   rt fn       ae      -> T.Scanl1 rt (lam2 tenv fn) (aexp tenv ae)
       T.Scanr    rt fn einit ae      -> T.Scanr  rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanr'   rt fn einit ae      -> T.Scanr' rt (lam2 tenv fn) (exp tenv einit) (aexp tenv ae)
       T.Scanr1   rt fn       ae      -> T.Scanr1 rt (lam2 tenv fn) (aexp tenv ae)

       T.Permute rt fn2 ae1 fn1 ae2 -> 
         T.Permute rt (lam2 tenv fn2) (aexp tenv ae1) 
                      (lam1 tenv fn1) (aexp tenv ae2)

       T.Backpermute rt ex lam ae -> T.Backpermute rt (exp tenv ex) (lam1 tenv lam) (aexp tenv ae)
       T.Reshape     rt ex     ae -> T.Reshape     rt (exp tenv ex)                 (aexp tenv ae)
       T.Stencil   rt fn bndry ae -> T.Stencil     rt (lam1 tenv fn) bndry          (aexp tenv ae)
       T.Stencil2  rt fn bnd1 ae1 bnd2 ae2 ->  T.Stencil2 rt (lam2 tenv fn) bnd1 (aexp tenv ae1)
                                               bnd2 (aexp tenv ae2)
   -- Handle arity 1 lambdas:
   lam1 tenv (S.Lam1 (v,ty) bod) = S.Lam1 (v,ty) (exp tenv' bod)
     where tenv' = M.insert v ty tenv
   -- Handle arity 2 lambdas:
   lam2 tenv (S.Lam2 (v1,ty1) (v2,ty2) bod) = S.Lam2 (v1,ty1) (v2,ty2) (exp tenv' bod)
     where tenv' = M.insert v1 ty1 $ M.insert v2 ty2 tenv

   exp :: M.Map S.Var S.Type -> T.Exp -> T.Exp 
   exp tenv e = 
     case e of  
       -- T.EIndex els -> error "staticTupleIndices: EIndex is slated to be removed"

       -- -- TODO: Eliminate
       -- T.EIndexConsDynamic e1 e2 -> 
       --   -- This is potentially inefficient.
       --   error$"IndexCons - finish me"
         
       -- T.EIndexHeadDynamic e -> error "unimplemented: eliminate indexheaddynamic"
       -- T.EIndexTailDynamic e -> error "unimplemented: eliminate indextaildynamic"

       
       -- The rest is BOILERPLATE:
       ------------------------------------------------------------
       T.EVr vr -> T.EVr vr       
       T.ELet (vr,ty,rhs) bod -> T.ELet (vr,ty, exp tenv' rhs) (exp tenv bod)
         where tenv' = M.insert vr ty tenv
       T.EPrimApp ty p args -> T.EPrimApp ty p (L.map (exp tenv) args)
       T.ECond e1 e2 e3 -> T.ECond (exp tenv e1) (exp tenv e2) (exp tenv e3)
       T.EIndexScalar ae ex -> T.EIndexScalar (aexp tenv ae) (exp tenv ex)
       T.EShapeSize ex -> T.EShapeSize (exp  tenv ex)
       T.EShape     ae -> T.EShape     (aexp tenv ae)

       T.EConst c  -> T.EConst c 
       T.ETuple ls -> T.ETuple (L.map (exp tenv) ls)
       T.ETupProjectFromRight ind ex -> T.ETupProjectFromRight ind (exp tenv ex)
       
       T.EIndex els -> T.EIndex (L.map (exp tenv) els)
       T.EIndexConsDynamic e1 e2 -> T.EIndexConsDynamic (exp tenv e1) (exp tenv e2)
       T.EIndexHeadDynamic ex -> T.EIndexHeadDynamic (exp tenv ex)
       T.EIndexTailDynamic ex -> T.EIndexTailDynamic (exp tenv ex)

