{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ParallelListComp #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A pass to convert multidimensional arrays into one-dimensional
-- arrays, including computing flat indices from multi-dimensional
-- (tuple) ones.
--
-- NOTE: Ideally this pass would be split into two, and the first pass
-- could inject explicit index collapse/expand operations.  These
-- could be optimized, with consecutive expand/collapse or
-- collapse/expand canceling out.  Then a separate pass could inject
-- the actual conversion arithmetic.

module Data.Array.Accelerate.BackendKit.Phase2.OneDimensionalize (oneDimensionalize) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.State.Strict
import Control.Monad.Reader
import Text.PrettyPrint.GenericPretty (Out(doc))

import qualified Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.IRs.Metadata (ArraySizeEstimate(..), FoldStrides(..))
import Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, mkIndTy, mkPrj,
                                                       maybeLet, addI, mulI, quotI, remI)
import Data.Array.Accelerate.BackendKit.CompilerUtils (shapeName)  

-- | Configuration parameter.  This controls whether we take advantage
-- of OpenCL/CUDA's native support for 2D and 3D kernels.  If this is
-- turned ON then we do unnecessary quotient/remainder operations to
-- compute multidimensional indices FROM flat indices at runtime.
flattenGenerates :: Bool
flattenGenerates = True

--------------------------------------------------------------------------------

type MyM a = ReaderT (Prog ArraySizeEstimate) GensymM a 


-- | The pass itself.
oneDimensionalize :: Prog ArraySizeEstimate -> (Prog (ArraySizeEstimate))
oneDimensionalize  prog@Prog{progBinds, progType, uniqueCounter, typeEnv } =
--    (FoldStrides undefined, prog')
      (prog')
  where
    prog' = prog { progBinds    = binds,
                   progType     = doTy progType, 
                   uniqueCounter= newCount,
                   -- Rebuild this because types change due to ranks becoming 1:
                   typeEnv      = M.fromList$ map (\(ProgBind v t _ _) -> (v,t)) binds
                 }
    m1 = mapM (doBind typeEnv) progBinds
    m2 = runReaderT m1 prog
    (binds,newCount) = runState m2 uniqueCounter

compute1DSize :: Int -> Exp -> MyM Exp
compute1DSize ndim eSz = do
   -- The one-dimensional size is just the product of the dimensions:
   lift$ maybeLet eSz (mkIndTy ndim)
          (\tmp -> foldl mulI (EConst (I 1))
                   [ mkPrj i 1 ndim (EVr tmp) | i <- reverse[0 .. ndim-1] ])


-- | Get the size of the inner most dimension, which is the stride between
--   separately-folded sections.
getFoldStride :: M.Map Var Type -> M.Map Var Exp -> ProgBind ArraySizeEstimate -> M.Map Var Exp
getFoldStride env acc (ProgBind vo aty sz eith) =
  case eith of
    Left _ -> acc
    Right ae -> 
     case ae of 
       Fold _ _ vi       -> M.insert vo (innDim vi) acc
       Fold1 _  vi       -> M.insert vo (innDim vi) acc
       FoldSeg  _ _ vi _ -> M.insert vo (innDim vi) acc 
       Fold1Seg _   vi _ -> M.insert vo (innDim vi) acc
       Scanl    _ _ vi   -> M.insert vo (innDim vi) acc
       Scanl'   _ _ vi   -> M.insert vo (innDim vi) acc
       Scanl1   _   vi   -> M.insert vo (innDim vi) acc
       Scanr    _ _ vi   -> M.insert vo (innDim vi) acc
       Scanr'   _ _ vi   -> M.insert vo (innDim vi) acc
       Scanr1   _   vi   -> M.insert vo (innDim vi) acc
       
       _                 -> acc
  where
    innDim inV = 
      case sz of
        KnownSize ls -> EConst$ I$ last ls
        UnknownSize ->
          let shp   = shapeName inV in
          -- Take the "last" of a tuple:
          case env M.! shp of
            TInt      -> EVr shp
            TTuple ls -> ETupProject 0 1 (EVr shp)
            ty        -> error$"OneDimensionalize.hs: Should not have a shape of this type: "++show ty


-- Map Var (ProgBind (a,b,Cost)) -> 
doBind :: M.Map Var Type -> ProgBind ArraySizeEstimate -> MyM (ProgBind ArraySizeEstimate)
doBind env (ProgBind vo t sz (Left  ex)) = (ProgBind vo (doTy t) (doSz sz) . Left)  <$> doExp env ex
--doBind (ProgBind vo t sz (Right ex)) = (ProgBind vo (doTy t) (doSz sz) . Right) <$> mapMAE doE ex

doBind env pb@(ProgBind vo aty sz (Right ae)) =
   (ProgBind vo (doTy aty) (doSz sz) . Right) <$>
  case ae of

    -- For OpenCL/CUDA, we need to do flattening if the array is >3D anyway.
    -- Presently we always flatten to 1D, but in the future we may want to allow 2D
    -- and 3D.
    Generate eSz (Lam1 (indV,indTy) bod) | flattenGenerates || ndim > 3 -> do
    -- For Generate, we need to change the size argument and the type expected by the kernel.
      eSz''  <- compute1DSize ndim =<< doE eSz
      bod'   <- doExp (M.insert indV indTy env) bod
      tmp    <- lift$ genUniqueWith "flatidx"
      newidx <- unFlatIDX pb (EVr tmp)
      return$ Generate eSz'' $
               Lam1 (tmp,TInt) $
                ELet (indV, indTy, newidx) bod'

    -- BOILERPLATE:
    ------------------------------------------------------------
    Generate e lam1         -> Generate <$> doE e <*> doLam1 lam1
    Use _                   -> return ae
    Vr _                    -> return ae
    Unit ex                 -> Unit <$> doE ex
    Cond a b c              -> Cond <$> doE a <*> return b <*> return c
    Fold     lam2 e v       -> Fold     <$> doLam2 lam2 <*> doE e <*> return v
    Fold1    lam2 v         -> Fold1    <$> doLam2 lam2 <*> return v
    FoldSeg  lam2 e v w     -> FoldSeg  <$> doLam2 lam2 <*> doE e <*> return v <*> return w
    Fold1Seg lam2 v w       -> Fold1Seg <$> doLam2 lam2 <*> return v <*> return w
    Scanl    lam2 e v       -> Scanl    <$> doLam2 lam2 <*> doE e <*> return v
    Scanl'   lam2 e v       -> Scanl'   <$> doLam2 lam2 <*> doE e <*> return v
    Scanl1   lam2   v       -> Scanl1   <$> doLam2 lam2           <*> return v
    Scanr    lam2 e v       -> Scanr    <$> doLam2 lam2 <*> doE e <*> return v
    Scanr'   lam2 e v       -> Scanr'   <$> doLam2 lam2 <*> doE e <*> return v
    Scanr1   lam2   v       -> Scanr1   <$> doLam2 lam2           <*> return v
    Permute  lam2 v lam1 w  -> Permute  <$> doLam2 lam2 <*> return v
                                        <*> doLam1 lam1 <*> return w
    Stencil  lam1 b v       -> Stencil  <$> doLam1 lam1 <*> return b <*> return v
    Stencil2 lam2 b v c w   -> Stencil2 <$> doLam2 lam2 <*> return b <*> return v <*> return c <*> return w
    Map      _ _        -> err
    ZipWith  _ _ _      -> err
    Reshape  _ _        -> err
    Backpermute _ _ _   -> err
    Replicate _ _ _     -> err
    Index  _ _ _        -> err
 where
   doE = doExp env
   err = doerr ae
   TArray ndim _elty = aty

   doLam2 (Lam2 (v,t1) (w,t2) bod) =
     Lam2 (v,t1) (w,t2) <$>
       doExp (M.insert v t1 $ M.insert w t2 env) bod
   doLam1 (Lam1 (v,t) bod) =
     Lam1 (v,t) <$> doExp (M.insert v t env) bod

doSz :: ArraySizeEstimate -> ArraySizeEstimate
doSz (KnownSize ls) = KnownSize$ [product ls]
doSz UnknownSize    = UnknownSize

doTy :: Type -> Type
doTy (TArray _ elt) = TArray 1 elt
doTy (TTuple ls)    = TTuple$ map doTy ls
doTy ty             = ty 

doExp :: M.Map Var Type -> Exp -> MyM Exp
doExp env ex = 
  case ex of
    -- This is where we inject a polynomial to do indexing:
    EIndexScalar avr indE -> do
      tmp  <- lift genUnique 
      prog <- ask
      let (Just pb@(ProgBind _ (TArray n _) _ (Right _))) =
            lookupProgBind avr (progBinds prog)
      return$
        ELet (tmp, mkIndTy n, indE)
         (EIndexScalar avr (makeFlatIDX pb (EVr tmp)))
    
    EShape _            -> doerr ex 
    EShapeSize _        -> doerr ex
    EVr _               -> return ex
    EConst _            -> return ex
    ECond e1 e2 e3      -> ECond   <$> doExp env e1 <*> doExp env e2 <*> doExp env e3
    ELet (v,t,rhs) bod  -> (\r b -> ELet (v,t,r) b) <$> doExp env rhs <*> doExp (M.insert v t env) bod
    ETupProject i l e   -> ETupProject i l  <$> doExp env e
    EPrimApp p t els    -> EPrimApp    p t  <$> mapM (doExp env) els
    ETuple els          -> ETuple           <$> mapM (doExp env) els
    EIndex _            -> doerr ex

-- | Construct a polynomial expression that computes the flat-index
--   into the array produced by the ProgBind argument.  The second
--   argument is a trivial expression (like a variable) that holds the
--   desired (multidimensional) index.
makeFlatIDX :: ProgBind ArraySizeEstimate -> Exp -> Exp
makeFlatIDX pb@(ProgBind _ aty _ _) idxE = polynom
  where
    coefs = getIdxCoefs pb
    TArray ndim _ = aty
    polynom = foldl addI (EConst (I 0))
               [ mulI coef (mkPrj ind 1 ndim idxE) 
               | ind  <- reverse [ 0 .. ndim - 1 ]
               | coef <- coefs ]
  
-- | This function does the inverse.  It uses quotient/remainder to
-- figure out the original multidimensional indices from the flat index.
unFlatIDX :: ProgBind ArraySizeEstimate -> Exp -> MyM Exp
unFlatIDX pb@(ProgBind _ aty _ _) flatidxE = do
    tmps <- lift$ sequence $ replicate (2*ndim) (genUniqueWith "idx1D")
    let loop [] [] _ acc = ETuple$ map EVr acc
        loop (tmp1:tmp2:tmpsRst) (coef1:coefsRst) leftover acc =
          -- Inefficient: no combined quotient/remainder operation.
          ELet (tmp1, TInt, quotI leftover coef1) $
          ELet (tmp2, TInt, remI  leftover coef1) $
           loop tmpsRst coefsRst (EVr tmp2) (tmp1:acc)
        loop _ _ _ _ = error "OneDimensionalize.hs: the impossible happened."
    return$ loop tmps (reverse coefs) flatidxE []
  where    
    TArray ndim _ = aty
    coefs = getIdxCoefs pb    

-- | Get the set of coefficients that are needed for converting both
-- to and from a flat representation.
getIdxCoefs :: ProgBind ArraySizeEstimate -> [Exp]
getIdxCoefs (ProgBind nm aty sz _) =
  let (TArray ndims _) = aty in
  case sz of
    KnownSize ls -> map (EConst . I ) $ init$ scanl (*) 1 ls
    UnknownSize  ->
      let shapeLs = [ mkPrj i 1 ndims (EVr$ shapeName nm)
                    | i <- reverse [0 .. ndims-1] ] in 
      init$ scanl (mulI) (EConst (I 1)) shapeLs

doerr :: Out a => a -> t
doerr e = error$ "OneDimensionalize.hs: the following should be desugared before this pass is called:\n   "
          ++ show (doc e)

       
----------------------------------------------------------------------------------------------------
