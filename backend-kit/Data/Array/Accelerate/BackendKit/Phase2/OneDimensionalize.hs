{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ParallelListComp #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A pass to convert multidimensional arrays into one-dimensional
-- arrays, including computing flat indices from multi-dimensional
-- (tuple) ones.
-- 
-- This pass also introduces _size variables annalogous to the _shape variables (see
-- sizeName, shapeName).  After this pass the original shape variables should not be
-- counted on by future passes (e.g. they will eventually get detupled).
--
-- Finally, because this pass is the last one that deals with multi-dimensional
-- shapes, it extracts the innermost dimension sizes that determine fold strides.

module Data.Array.Accelerate.BackendKit.Phase2.OneDimensionalize (oneDimensionalize) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.State.Strict
import Control.Monad.Reader
import Text.PrettyPrint.GenericPretty (Out(doc))
import qualified Data.Map as M
import Debug.Trace

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.IRs.Metadata (ArraySizeEstimate(..), Stride(..))
import Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, mkIndTy, mkPrj,
                                                       maybeLetAllowETups, addI, mulI, quotI, remI)
import Data.Array.Accelerate.BackendKit.Utils.Helpers (shapeName, sizeName, maybtrace)

-- | Configuration parameter.  This controls whether we take advantage
-- of OpenCL/CUDA's native support for 2D and 3D kernels.  If this is
-- turned ON then we do unnecessary quotient/remainder operations to
-- compute multidimensional indices FROM flat indices at runtime.
flattenGenerates :: Bool
flattenGenerates = True

--------------------------------------------------------------------------------

-- | The pass itself.  See the module documentation.
--
-- NOTE: Ideally this pass would be split into two, and the first pass
-- could inject explicit index collapse/expand operations.  These
-- could be optimized, with consecutive expand/collapse or
-- collapse/expand canceling out.  Then a separate pass could inject
-- the actual conversion arithmetic.
oneDimensionalize :: Prog ArraySizeEstimate -> (Prog (Maybe (Stride Exp), ArraySizeEstimate))
oneDimensionalize  prog@Prog{progBinds, progType, uniqueCounter, typeEnv } =
      prog'
  where
    prog' = prog { progBinds    = binds3,
                   progType     = doTy progType, 
                   uniqueCounter= newCount,
                   -- Rebuild this because types change due to ranks becoming 1:
                   --  AND because of introduced _size variables:
                   typeEnv      = M.fromList$ map (\(ProgBind v t _ _) -> (v,t)) binds3
                 }
    binds1 = addSizes progBinds
    (binds2,newCount) = let m1 = mapM (doBind typeEnv) binds1
                            m2 = runReaderT m1 prog
                        in runState m2 uniqueCounter
    binds3 = map (getFoldStride typeEnv progBinds) binds2


type MyM a = ReaderT (Prog ArraySizeEstimate) GensymM a 

-- This version expects a 
compute1DSize :: Int -> Exp -> Exp
compute1DSize ndim ex =
  maybtrace ("[DBG OneDimensionalize]Computing 1D size for ndims "++show ndim++" input exp "++show ex)$  
  case ex of
    EVr    _ -> deflt
    ETuple _ -> deflt
    _        -> error$"compute1DSize: expected EVr or ETuple, got: "++show ex
 where
   -- The one-dimensional size is just the product of the dimensions:   
   deflt = foldl mulI (EConst (I 1))
           [ mkPrj i 1 ndim ex | i <- reverse[0 .. ndim-1] ]
{--
-- | This version also may introduce let bindings.
compute1DSizeM :: Int -> Exp -> MyM Exp
compute1DSizeM ndim eShp = do
   lift$ maybeLetAllowETups eShp (mkIndTy ndim) (compute1DSize ndim)
--}

-- | After the other processing is done, this goes back and adds the scalar bindings
-- to hold the (1D) sizes.
addSizes :: [ProgBind ArraySizeEstimate] -> [ProgBind ArraySizeEstimate]
addSizes [] = []
-- FIXME: Scanl' invalidates this:
addSizes (orig@(ProgBind vo (TArray ndim _) UnknownSize _) : rest) =
  (ProgBind (sizeName vo) TInt UnknownSize (Left$ compute1DSize ndim (EVr$ shapeName vo))) 
  : orig : addSizes rest
addSizes (hd:tl) = hd : addSizes tl

--------------------------------------------------------------------------------

-- | Get the size of the inner most dimension, which is the stride between
--   separately-folded sections.
getFoldStride :: M.Map Var Type -> [ProgBind ArraySizeEstimate] -> 
                 ProgBind ArraySizeEstimate ->
                 ProgBind (Maybe (Stride Exp), ArraySizeEstimate)
getFoldStride env allbinds (ProgBind vo outTy osz eith) =
  ProgBind vo outTy (newdec, osz) eith
 where
   
 newdec :: Maybe (Stride Exp)  
 newdec = 
  case eith of
    Left _ -> Nothing
    Right ae -> 
     case ae of 
       Fold _ _ vi       -> Just$ deftl vi
       Fold1 _  vi       -> Just$ deftl vi
       FoldSeg  _ _ _ _  -> Just$ error "OneDimensionalize.hs: UNFINISHED need to compute strides for foldsegs"
       Fold1Seg _   _ _  -> Just$ error "OneDimensionalize.hs: UNFINISHED need to compute strides for foldsegs"
       Scanl    _ _ _    -> Just$ StrideAll 
       Scanl'   _ _ _    -> Just$ StrideAll 
       Scanl1   _   _    -> Just$ StrideAll 
       Scanr    _ _ _    -> Just$ StrideAll 
       Scanr'   _ _ _    -> Just$ StrideAll 
       Scanr1   _   _    -> Just$ StrideAll 
       _                 -> Nothing

 deftl inArr =
   case outTy of
     -- When we're folding up the whole array, we just encode that as
     -- StrideAll, not bothering to track exactly how many elements it is.
     TArray 0 _ -> StrideAll
     _          -> StrideConst $ innDim inArr
            
 innDim inArr =
   let Just (ProgBind _ _ inSz _) = lookupProgBind inArr allbinds in   
   case inSz of
     KnownSize ls -> EConst$ I$ head ls
     UnknownSize ->
       let shp   = shapeName inArr in
       -- Take the "last" of a tuple:
       case M.lookup shp env of
         Just TInt       -> EVr shp
         Just (TTuple _) -> ETupProject 0 1 (EVr shp)
         Just ty         -> error$"OneDimensionalize.hs: Should not have a shape of this type: "++show ty
         Nothing         -> error$"OneDimensionalize.hs: Could not find shapename "++show shp++" in env:\n"++show env

--------------------------------------------------------------------------------

-- Map Var (ProgBind (a,b,Cost)) -> 
-- Comment: what is this for? 
doBind :: M.Map Var Type -> ProgBind ArraySizeEstimate -> MyM (ProgBind ArraySizeEstimate)
doBind env (ProgBind vo t sz (Left  ex)) = (ProgBind vo (doTy t) (doSz sz) . Left)  <$> doExp env ex
--doBind (ProgBind vo t sz (Right ex)) = (ProgBind vo (doTy t) (doSz sz) . Right) <$> mapMAE doE ex

doBind env pb@(ProgBind vo aty sz (Right ae)) =
   (ProgBind vo (doTy aty) (doSz sz) . Right) <$>
  case ae of

    -- For OpenCL/CUDA, we need to do flattening if the array is >3D anyway.
    -- Presently we always flatten to 1D, but in the future we may want to allow 2D
    -- and 3D.
    Generate _eShp (Lam1 (indV,indTy) bod) | flattenGenerates || ndim > 3 -> do
    -- For Generate, we need to change the size argument and the type expected by the kernel.
--      eShp''  <- compute1DSizeM ndim =<< doE eShp
      -- Interestingly, we need make no reference to eShp:
      let eShp'' = case sz of
                     UnknownSize  -> EVr$ sizeName vo
                     KnownSize ls -> EConst$ I$ product ls
      tmp    <- lift$ genUniqueWith "flatidx"
      newidx <- unFlatIDX pb (EVr tmp)

      Generate eShp'' . Lam1 (tmp,TInt) <$> do 
        maybeLetM indTy newidx $ \ indV' -> do 
          -- bod is already written to expect indV, fix it:
          let bod2 = substExp indV (EVr indV') bod
          doExp (M.insert indV indTy env) bod2                   

    -- BOILERPLATE:
    ------------------------------------------------------------
    Generate e lam1         -> Generate <$> doE e <*> doLam1 lam1
    Use    (AccArray dims payls) -> return$ Use $ AccArray [product dims] payls
    Use' v dims ty          -> return$ Use' v [product dims] ty    
--    Use' v (AcccArray dims payls) -> return$ Use' v $ AccArray [product dims] payls
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

-- What is the env for here ? it seems to not be used, and not part of result ? 
doExp :: M.Map Var Type -> Exp -> MyM Exp
doExp env ex = 
  case ex of
    -- This is where we inject a polynomial to do indexing:
    EIndexScalar avr indE -> do
      tmp  <- lift genUnique 
      prog <- ask
      let (Just pb@(ProgBind _ (TArray n _) _ (Right _))) =
            lookupProgBind avr (progBinds prog)
      maybeLetM (mkIndTy n) indE $ \ tmp -> 
        return (EIndexScalar avr (makeFlatIDX pb (EVr tmp)))
    
    EShape _            -> doerr ex 
    EShapeSize _        -> doerr ex
    EVr _               -> return ex
    EConst _            -> return ex
    EWhile (Lam1 (v1,t1) bod1) (Lam1 (v2,t2) bod2) e -> 
          EWhile  <$> (Lam1 (v1,t1) <$> doExp (M.insert v1 t1 env) bod1) 
                  <*> (Lam1 (v2,t2) <$> doExp (M.insert v2 t2 env) bod2) <*> doExp env e 
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
    let loop [] [] _ acc = return (ETuple$ map EVr acc)
        loop (_tmp1:_tmp2:tmpsRst) (coef1:coefsRst) leftover acc =
          -- Inefficient: no combined quotient/remainder operation.
          maybeLetM TInt (quotI leftover coef1) $ \ tmp1 -> 
           maybeLetM TInt (remI  leftover coef1) $ \ tmp2 -> 
            loop tmpsRst coefsRst (EVr tmp2) (tmp1:acc)
        loop _ _ _ _ = error "OneDimensionalize.hs: the impossible happened."
    loop tmps (reverse coefs) flatidxE []
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


-- | Bind a let expression only if necessary.  Don't introduce
-- variable-variable copies.
-- maybeLetM :: Exp -> Type -> (Var -> GensymM Exp) -> GensymM Exp
maybeLetM :: Type -> Exp -> (Var -> MyM Exp) -> MyM Exp
maybeLetM ty  ex dobod =
  case ex of
    EVr v -> dobod v
    _ -> do tmp <- lift $ genUnique
            bod <- dobod tmp
            return (ELet (tmp,ty,ex) bod)


-- This version avoids the issue of picking a monad, but is ugly to use:
-- maybeLet :: Exp -> Type -> GensymM (Var, Exp -> Exp)
-- maybeLet ex ty =
--   case ex of
--     EVr v -> return (v, id)
--     _ -> do tmp <- genUnique
--             return (tmp, \bod -> ELet (tmp,ty,ex) bod)

