{-# Language NamedFieldPuns, TupleSections #-}
{-# Language ParallelListComp #-}

module Data.Array.Accelerate.BackendKit.Phase2.UnzipArrays (unzipArrays) where
import Control.Monad.State.Strict
import Control.Applicative ((<$>),(<*>), pure)
import qualified Data.Map              as M

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendKit.Utils.Helpers ((#),isTrivialE)
import Data.Array.Accelerate.BackendKit.IRs.Metadata (SubBinds(..), OpInputs(..))
import Data.Array.Accelerate.BackendKit.CompilerUtils (maybtrace)
--------------------------------------------------------------------------------


-- | This pass commits to unzipped arrays.  It makes the leap between referring to
-- arrays in their zipped (array of tuples) form to their unzipped components.
-- 
-- Alas, because we are stuck with the Prog IR at this juncture, we yet can't fully
-- rewrite the AST to reflect this change..  However, after this pass the regular
-- variable fields of array op `ProgBinds` are IGNORED and the REAL names are found
-- in the SubBinds decorators.
--
-- Another way that we draw outside the lines of the Prog type, is that we nuke the
-- INPUTS to array operators.  Those refer, naturally, to the pre-unzipped arrays.
-- Instead we list the inputs explicitly in a new decoration.  Scalar expression
-- arguments to array operators are left alone, and they may still be tuples
-- (e.g. the initial element of a Fold).
--
-- Also, this pass does copy-prop at the array level.  After this pass array level
-- `Vr` should not occur.
--
-- This pass eliminates ETupProject's around EIndexScalar's.
unzipArrays :: S.Prog (SubBinds,a) -> S.Prog (OpInputs,(SubBinds,a))
unzipArrays prog@Prog{progBinds,progResults = WithShapesUnzipped pR } =
  prog { progBinds   = doBinds M.empty progBinds,
         -- All parts of an unzipped array have the same shape:         
         progResults = WithShapesUnzipped$
                       concatMap (\ (v,s) -> map (,s) (env # v)) pR
         -- Note: typeEnv already has the unzipped types.              
       }
  where
    env = M.fromList$
          map (\(ProgBind v _ (SubBinds vrs _,_) _) -> (v,vrs)) progBinds

-- | For this pass every top level binding is tracked in the environment which is
-- passed throuh the helper functions.
type Env = M.Map Var [Var]

doBinds :: Env -> [ProgBind (SubBinds,a)] -> [ProgBind (OpInputs,(SubBinds,a))]
doBinds _ [] = [] 
doBinds env (ProgBind vo _ _ (Right (Vr v1)) : rest) =
  -- Copy propagataion:
  doBinds (M.insert vo (env#v1) env) rest

-- Unzip Use to make things easier for future passes:
doBinds env (ProgBind vo aty (SubBinds {subnames,arrsize},d2) (Right (Use (AccArray {arrDim,arrPayloads}))) : rest) 
  | length subnames > 1 = 
    [ ProgBind subname arrty
               (OpInputs [], (SubBinds {subnames=[subname], arrsize=arrsize},d2))
               (Right (Use (AccArray { arrDim, arrPayloads = [onepayl] })))
    | subname <- subnames
    | arrty   <- S.flattenArrTy aty
    | onepayl <- arrPayloads  
    ]
    ++ doBinds (M.insert vo subnames env) rest

doBinds env (ProgBind vo ty dec@(SubBinds {subnames},_) op : rest) =
  ProgBind nukedVar ty (dec',dec) op' :
  doBinds (M.insert vo subnames env) rest
  where
    (dec',op') =
      case op of
        Left  ex -> (OpInputs[], Left$  doE  env ex)        
        Right ae -> let (ls,ae') = doAE env ae in
                    (OpInputs ls,Right ae')

-- | Returns (unzipped) operator INPUTS.
doAE :: Env -> AExp -> ([[Var]], AExp)
doAE env ae =
  case ae of
    Use _               -> ([],ae)
    Cond a b c          -> ([sp b,sp c], Cond (exp a) nukedVar nukedVar)
    Generate e lam1     -> ([], Generate (exp e) (doLam1 lam1))
    Fold lam2 e v       -> ([sp v],Fold  (doLam2 lam2) (exp e) nukedVar)
    Fold1    lam2 v     -> ([sp v],Fold1 (doLam2 lam2)         nukedVar)
    FoldSeg  lam2 e v w -> ([sp v,sp w],FoldSeg  (doLam2 lam2) (exp e) nukedVar nukedVar)
    Fold1Seg lam2 v w   -> ([sp v,sp w],Fold1Seg (doLam2 lam2)         nukedVar nukedVar)
    Scanl    lam2 e v   -> ([sp v],Scanl  (doLam2 lam2) (exp e) nukedVar)
    Scanl'   lam2 e v   -> ([sp v],Scanl' (doLam2 lam2) (exp e) nukedVar)
    Scanl1   lam2   v   -> ([sp v],Scanl1 (doLam2 lam2)         nukedVar)
    Scanr    lam2 e v   -> ([sp v],Scanr  (doLam2 lam2) (exp e) nukedVar)
    Scanr'   lam2 e v   -> ([sp v],Scanr' (doLam2 lam2) (exp e) nukedVar)
    Scanr1   lam2   v   -> ([sp v],Scanr1 (doLam2 lam2)         nukedVar)
    Stencil  lam1 b v   -> ([sp v],Stencil (doLam1 lam1) b nukedVar)
    Stencil2 l2 b v c w -> ([sp v,sp w],Stencil2 (doLam2 l2) b nukedVar c nukedVar)
    Permute l2 v l1 w   -> ([sp v,sp w],Permute (doLam2 l2) nukedVar (doLam1 l1) nukedVar)
    Unit {}             -> err ae
    Map  {}             -> err ae
    ZipWith {}          -> err ae
    Backpermute {}      -> err ae
    Replicate {}        -> err ae
    Reshape   {}        -> err ae
    Index     {}        -> err ae
    Vr _                -> error "impossible, but GHC doesn't know it"
 where
   sp v = case M.lookup v env of
            Nothing -> error$"UnzipArrays.hs/doAE: could not find SubBinds for "++show v
            Just x  -> x
   exp = doE env
   -- We're NOT detupling scalar vars at this point, so we don't bother extending the env:
   doLam1 (Lam1 (v,ty) bod) = Lam1 (v,ty) (doE env bod)
   doLam2 (Lam2 b1 b2 bod)  = Lam2 b1 b2 (doE env bod)

doE :: M.Map Var [Var] -> Exp -> Exp
doE env ex =
  case ex of
    ETupProject ix len (EIndexScalar avr ind) ->
      if len /= 1 then error$"UnzipArrays.hs: ETupProject with len/=1: "++show ex
      else
        maybtrace ("Projecting out of "++show (env # avr)++" for avr "++show avr++" want index "++show ix)$
        EIndexScalar (reverse (env # avr) !! ix) (doE env ind)
    EIndexScalar avr e
      | isTrivialE e ->
        -- We may be forced to create an ETuple here, but it must be in tail position.
        -- TODO: AUDIT THIS FURTHER!
        -- TODO: thread gensym through so we can do MaybeLet here.
        mkETuple [ EIndexScalar avr' (doE env e) | avr' <- env#avr ]
      | otherwise -> error "UnzipArrays.hs: needed refactor here... push through GensymM..."
    ETupProject ix l e  -> ETupProject ix l (doE env e) 
    EShape _            -> err ex
    EShapeSize _        -> err ex
    EIndex _            -> err ex
    EConst _            -> ex
    EVr _               -> ex
    ECond e1 e2 e3      -> ECond (doE env e1) (doE env e2) (doE env e3)
    ELet (v,t,rhs) bod  -> ELet (v,t,doE env rhs) (doE env bod)
    ETuple els          -> ETuple       (map (doE env) els)
    EPrimApp p t els    -> EPrimApp p t (map (doE env) els)

err :: Show a => a -> b
err x = error$"UnzipArrays.hs: should have been eliminated before this pass: "++ show x

nukedVar :: Var
nukedVar = var ""
