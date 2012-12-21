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

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.IRs.Metadata (ArraySizeEstimate(..))
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
oneDimensionalize :: Prog ArraySizeEstimate -> Prog ArraySizeEstimate
oneDimensionalize  prog@Prog{progBinds, uniqueCounter } = 
  prog { progBinds    = binds, 
         uniqueCounter= newCount }
  where
    m1 = mapM doBind progBinds
    m2 = runReaderT m1 prog
    (binds,newCount) = runState m2 uniqueCounter

-- Map Var (ProgBind (a,b,Cost)) -> 
doBind :: ProgBind ArraySizeEstimate -> MyM (ProgBind ArraySizeEstimate)
doBind (ProgBind vo t sz (Left  ex)) = (ProgBind vo (doTy t) (doSz sz) . Left)  <$> doE ex
--doBind (ProgBind vo t sz (Right ex)) = (ProgBind vo (doTy t) (doSz sz) . Right) <$> mapMAE doE ex

doBind pb@(ProgBind vo aty sz (Right ae)) = (ProgBind vo (doTy aty) (doSz sz) . Right) <$>
  case ae of
    -- For Generate, we need to change the size argument and the type expected by the kernel.
    Generate eSz (Lam1 (indV,indTy) bod) | flattenGenerates || ndim > 3 -> do
      -- With no OpenCL/CUDA support, we need to do flattening if the
      -- array is >3D anyway.  TODO!  This is backend specific.  We
      -- may want to change it for a CPU/Cilk backend.
      eSz'   <- doE eSz
      -- The one-dimensional size is just the product of the dimensions:
      eSz''  <- lift$ maybeLet eSz' (mkIndTy ndim)
                       (\tmp -> foldl mulI (EConst (I 1))
                                 [ mkPrj i 1 ndim (EVr tmp) | i <- reverse[0 .. ndim-1] ])
      bod'   <- doE bod
      tmp    <- lift$ genUniqueWith "flatidx"
      newidx <- unFlatIDX pb (EVr tmp)
      return$ Generate eSz'' $
               Lam1 (tmp,TInt) $
                ELet (indV, indTy, newidx) bod'

    -- BOILERPLATE:
    ------------------------------------------------------------
    Generate e (Lam1 arg bod)         -> Generate <$> doE e <*> (Lam1 arg <$> doE bod)
    Use _                             -> return ae
    Vr _                              -> return ae
    Unit ex                           -> Unit <$> doE ex
    Cond a b c                        -> Cond <$> doE a <*> return b <*> return c
    Fold     (Lam2 a1 a2 bod) e v     -> Fold     <$> (Lam2 a1 a2 <$> doE bod) <*> doE e <*> return v
    Fold1    (Lam2 a1 a2 bod) v       -> Fold1    <$> (Lam2 a1 a2 <$> doE bod) <*> return v
    FoldSeg  (Lam2 a1 a2 bod) e v w   -> FoldSeg  <$> (Lam2 a1 a2 <$> doE bod) <*> doE e <*> return v <*> return w
    Fold1Seg (Lam2 a1 a2 bod) v w     -> Fold1Seg <$> (Lam2 a1 a2 <$> doE bod) <*> return v <*> return w
    Scanl    (Lam2 a1 a2 bod) e v     -> Scanl    <$> (Lam2 a1 a2 <$> doE bod) <*> doE e <*> return v
    Scanl'   (Lam2 a1 a2 bod) e v     -> Scanl'   <$> (Lam2 a1 a2 <$> doE bod) <*> doE e <*> return v
    Scanl1   (Lam2 a1 a2 bod)   v     -> Scanl1   <$> (Lam2 a1 a2 <$> doE bod)           <*> return v
    Scanr    (Lam2 a1 a2 bod) e v     -> Scanr    <$> (Lam2 a1 a2 <$> doE bod) <*> doE e <*> return v
    Scanr'   (Lam2 a1 a2 bod) e v     -> Scanr'   <$> (Lam2 a1 a2 <$> doE bod) <*> doE e <*> return v
    Scanr1   (Lam2 a1 a2 bod)   v     -> Scanr1   <$> (Lam2 a1 a2 <$> doE bod)           <*> return v
    Permute (Lam2 a1 a2 bod1) v (Lam1 a3 bod2) w -> Permute <$> (Lam2 a1 a2 <$> doE bod1) <*> return v
                                                            <*> (Lam1 a3    <$> doE bod2) <*> return w
    Stencil  (Lam1 a1    bod) b v     -> do bod' <- doE bod
                                            return$ Stencil  (Lam1 a1    bod') b v
    Stencil2 (Lam2 a1 a2 bod) b v c w -> do bod' <- doE bod
                                            return$ Stencil2 (Lam2 a1 a2 bod') b v c w
    -- Reshape shE v                     -> return (Vr v)
    -- Backpermute ex (Lam1 arg bod) vr  -> Backpermute <$> doE ex <*> (Lam1 arg <$> doE bod)  <*> return vr
    -- Replicate template ex vr          -> Replicate template <$> doE ex <*> return vr
    -- Index slc vr ex                   -> Index slc vr <$> doE ex
    -- Map      (Lam1 arg bod) vr        -> Map  <$> (Lam1 arg <$> doE bod) <*> return vr
    -- ZipWith  (Lam2 a1 a2 bod) v1 v2   -> ZipWith <$> (Lam2 a1 a2 <$> doE bod) <*> return v1 <*> return v2
    Map      _ _        -> err
    ZipWith  _ _ _      -> err
    Reshape  _ _        -> err
    Backpermute _ _ _   -> err
    Replicate _ _ _     -> err
    Index  _ _ _        -> err
 where
   err = doerr ae
   TArray ndim _elty = aty



doSz :: ArraySizeEstimate -> ArraySizeEstimate
doSz (KnownSize ls) = KnownSize$ [product ls]
doSz UnknownSize    = UnknownSize

doTy :: Type -> Type
doTy (TArray _ elt) = TArray 1 elt
doTy ty             = ty 

doE :: Exp -> MyM Exp
doE ex = 
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
    
    EShape avr          -> return$ EShape avr
    EShapeSize e        -> EShapeSize <$> doE e
    EVr _               -> return ex
    EConst _            -> return ex
    ECond e1 e2 e3      -> ECond   <$> doE e1 <*> doE e2 <*> doE e3
    ELet (v,t,rhs) bod  -> (\r b -> ELet (v,t,r) b) <$> doE rhs <*> doE bod
    ETupProject i l e   -> ETupProject i l  <$> doE e
    EPrimApp p t els    -> EPrimApp    p t  <$> mapM doE els
    ETuple els          -> ETuple           <$> mapM doE els
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
doerr e = error$ "OneDimensionalize.hs: the following should be desugared before this pass is called:\n   "++ show (doc e)

       
----------------------------------------------------------------------------------------------------
