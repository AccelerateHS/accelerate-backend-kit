{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A pass to get rid of EShape and Reshape and track unknown shapes
-- as explicit (scalar) variable bindings routed through the program.

module Data.Array.Accelerate.BackendKit.Phase2.ExplicitShapes where 

import           Control.Monad.Reader
import           Control.Monad.State.Strict (runState)
import           Control.Applicative ((<$>), (<*>))
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import           Data.List as L
import qualified Data.Map as M
import           Data.Maybe (fromJust)

import Data.Array.Accelerate.BackendKit.IRs.Metadata (ArraySizeEstimate(..))
import Data.Array.Accelerate.BackendKit.Utils.Helpers (mkIndTy, mkPrj, mulI, genUnique, genUniqueWith, GensymM,
                                                       (#), mkIndExp, maybtrace, shapeName, fragileZip3)
import Text.PrettyPrint.GenericPretty (Out(doc))


-- | A monad to use just for this pass.  Allows us to both generate symbols and read
-- the original (complete) input program to the pass.
type MyM a = ReaderT (Prog ArraySizeEstimate) GensymM a

--------------------------------------------------------------------------------

-- | The convention is that for every array variable "A" of
--   statically-unknown shape, a top-level binding "A_shape" will be
--   introduced which carries a tuple describing the shape of A.
--   Thus `(EShape A)` becomes simply `A_shape`.
--
--   GRAMMAR CHANGE: syntax forms parameterized by a shape expression
--   (Generate,BackPermute,Replicate) instead have only a variable reference in that
--   context after this pass.
--
--   NEW CONVENTION: This pass replaces the [arrV,arrV...] list of progResults with
--   pairs [(arrV,expV),(arrV,expV)...] list containing the results AND their
--   corresponding shapes.
explicitShapes :: Prog ArraySizeEstimate -> Prog ArraySizeEstimate
explicitShapes prog@Prog{progBinds, uniqueCounter, progResults } =
  case progResults of 
    -- If this pass has already run, we don't bother.  Hence this pass is idempotent.
    WithShapes    _ -> prog
    WithoutShapes _ -> newprog
    WithShapesUnzipped _ -> 
      error "explicitShapes: this pass should not be run so late in the compiler: WithShapesUnzipped" 
  where
   newprog = 
     prog { progBinds    = binds, 
            uniqueCounter= newCount,
            progResults  = WithShapes$ map (\v -> (v,shapeName v)) (resultNames progResults),
            -- Rebuild this cache due to new bindings:
            typeEnv      = M.fromList$ map (\(ProgBind v t _ _) -> (v,t)) binds
          }
   (binds,newCount) =
      runState (runReaderT (doBinds progBinds) prog) uniqueCounter

doBinds :: [ProgBind ArraySizeEstimate] -> MyM [ProgBind ArraySizeEstimate]
doBinds [] = return []
doBinds (ProgBind vo t sz (Left ex) : rest) =
  do ex'   <- doE ex
     rest' <- doBinds rest
     return (ProgBind vo t sz (Left ex') : rest')

doBinds (ProgBind vo voty sz (Right ae) : rest) = do
     rest' <- doBinds rest
     Prog{progResults} <- ask     
     case sz of
       KnownSize ls -> do
         ae' <- doAE ae
         let szEx = mkIndExp ls
             shapeBnd = if vo `elem` resultNames progResults then
                          [ProgBind (shapeName vo) (mkIndTy vo_ndims) UnknownSize (Left szEx) ]
                        else []
         return (ProgBind vo voty sz (Right ae') : shapeBnd ++ rest')
       UnknownSize -> do 
         (newBinds, szEx, ae') <- handleUnknownSize
         return$ newBinds ++
                 -- Here we inject the new shape binding:      
                 ProgBind (shapeName vo) (mkIndTy vo_ndims) UnknownSize (Left szEx) : 
                 ProgBind vo voty sz (Right ae') :
                 rest'      
  where
    vo_ndims = case voty of
                TArray n _ -> n
                a -> error $ "explicitShapes: doBinds got unexpected =" ++ show voty
--    TArray vo_ndims _ = voty

    -- handleUnknownSize returns:
    --   (1) a list of new binds
    --   (2) an expression describing the shape of the resulting array
    --   (3) a new AExp
    handleUnknownSize = (do
      prog@Prog{typeEnv} <- ask
      let getSizeE = mkSizeE prog
          -- Remove the inner dimension:
          knockOne v = maybtrace ("TEMPMSG - KNOCKING "++show v++" down to "++show (ndims-1)++" = "++ show x ++" sizeE "++show (getSizeE v))
                       x
            where
              TArray ndims t = typeEnv # v
              x = [ mkPrj i 1 ndims (getSizeE v) t
                  | i <- reverse [0..ndims-2]]
--                  | i <- reverse [1..ndims-1] 
                    
          -- RRN [2013.02.09] - This looks HIGHLY suspect ^^

          -- Replace the inner dimension.
          -- ASSUMPTION: segs is 1D and its shape is a TInt:
          replaceOne v segs =
            maybtrace ("TEMPMSG[ExplicitShapes] - REPLACEONE "++show(v,segs) ++" = "++  show (mkETuple$ (getSizeE segs) : knockOne v )) $
            mkETuple$ (getSizeE segs) : knockOne v 

          -- Beware tricky intersection semantics:
          intersectShapes v1 v2 =
              maybtrace ("TEMPMSG[ExplicitShapes] - INTERSECT SHAPES "++show(v1,v2) ++" supposed sizes "++show((getSizeE v1),(getSizeE v2)) ) $            
              let TArray v1Dims t1 = typeEnv # v1
                  TArray v2Dims t2 = typeEnv # v2 in
              if v1Dims /= v2Dims || v1Dims /= vo_ndims then
                error$"ExplicitShapes/intersectShapes: mismatched ranks: "++show (v1Dims, v2Dims, vo_ndims)
              else   
                mkETuple$ [ let a = mkPrj i 1 v1Dims (getSizeE v1) t1
                                b = mkPrj i 1 v2Dims (getSizeE v2) t1
                            in EPrimApp TInt (SP Min) [a,b]
                          | i <- reverse [0 .. v1Dims-1]]
      case ae of
        -- Desugaring reshape is as easy as pie.  Keep the array; change the shape.
        -- FIXME -- insert dynamic error checking here!!!
        Vr avr                            -> return ([], getSizeE avr, ae)
        Cond a bvr cvr                    -> do a'  <- doE a
                                                tmp <- lift genUnique
                                                return ([ProgBind tmp TBool UnknownSize (Left a')],
                                                        ECond (EVr tmp) (getSizeE bvr) (getSizeE cvr),
                                                        Cond (EVr tmp) bvr cvr)
        Reshape ex v                      -> do ex' <- doE ex
                                                return ([], ex', Vr v)
        Generate ex (Lam1 arg bod)        -> do bod' <- doE bod
                                                ex'  <- doE ex
                                                return ([], ex', Generate (EVr$shapeName vo) (Lam1 arg bod'))
        Backpermute ex (Lam1 arg bod) vr  -> do bod' <- doE bod
                                                ex'  <- doE ex                                                
                                                return ([], ex', Backpermute (EVr$shapeName vo) (Lam1 arg bod') vr)

        Map      (Lam1 arg bod) vr        -> do bod' <- doE bod
                                                return ([], getSizeE vr,           Map     (Lam1 arg bod') vr)
        ZipWith  (Lam2 a1 a2 bod) v1 v2   -> do bod' <- doE bod
                                                return ([], intersectShapes v1 v2, ZipWith (Lam2 a1 a2 bod') v1 v2)
        Stencil  (Lam1 a1    bod) b v     -> do bod' <- doE bod
                                                return ([], getSizeE v,            Stencil (Lam1 a1 bod') b v)
        Stencil2 (Lam2 a1 a2 bod) b v c w -> do bod' <- doE bod
                                                return ([], intersectShapes v w,   Stencil2 (Lam2 a1 a2 bod') b v c w)
        Fold     (Lam2 a1 a2 bod) e v     -> do bod' <- doE bod; e' <- doE e
                                                return ([], mkETuple$ knockOne v,  Fold  (Lam2 a1 a2 bod') e' v)
        Fold1    (Lam2 a1 a2 bod) v       -> do bod' <- doE bod
                                                return ([], mkETuple$ knockOne v,  Fold1 (Lam2 a1 a2 bod') v)
        -- -- The shape of the folded vector depends on how many segments there are:
        FoldSeg  (Lam2 a1 a2 bod) e v w   -> do bod' <- doE bod; e' <- doE e
                                                return ([], replaceOne v w,        FoldSeg  (Lam2 a1 a2 bod') e' v w)
        Fold1Seg (Lam2 a1 a2 bod)   v w   -> do bod' <- doE bod
                                                return ([], replaceOne v w,        Fold1Seg (Lam2 a1 a2 bod')    v w)
        -- Scans are one-dimensional:
        Scanl1   (Lam2 a1 a2 bod)   v     -> do bod' <- doE bod
                                                return ([], getSizeE v,            Scanl1   (Lam2 a1 a2 bod') v)
        Scanl    (Lam2 a1 a2 bod) e v     -> do bod' <- doE bod; e' <- doE e
                                                return ([], EPrimApp TInt (NP Add) [EConst (I 1), getSizeE v], 
                                                        Scanl (Lam2 a1 a2 bod') e' v)
        Scanr1   (Lam2 a1 a2 bod)   v     -> do bod' <- doE bod
                                                return ([], getSizeE v,       Scanr1   (Lam2 a1 a2 bod') v)
        Scanr    (Lam2 a1 a2 bod) e v     -> do bod' <- doE bod; e' <- doE e
                                                return ([], EPrimApp TInt (NP Add) [EConst (I 1), getSizeE v],
                                                        Scanr (Lam2 a1 a2 bod') e' v)
        Permute (Lam2 a1 a2 bod1) v (Lam1 a3 bod2) w ->
                                             do bod1' <- doE bod1; bod2' <- doE bod2
                                                return ([], getSizeE v, 
                                                        Permute (Lam2 a1 a2 bod1') v
                                                                (Lam1 a3    bod2') w)

        Replicate template ex upV ->
          do gensym <- lift $ genUniqueWith "replicTemplate" -- The new shape binding.
             prg    <- ask
             let -- Type of the new "template expression":
                 exTy = topLevelExpType prg ex
                 -- How many entries to be expect to be in 'ex' given the weird encoding:
                 numWithoutTrailing = length template - length (takeWhile (==All) (reverse template))
                 TArray upDims _ = typeEnv # upV
                 -- Build up the individual components of the shape of Replicate's output:
                 ls = [ case pr of 
                          -- The 'ex' expression will retain slots for the Alls that are ():
                          (Fixed,_indA,indF) -> mkPrj indF 1 numWithoutTrailing (EVr gensym) (error "ExplicitShapes: Replicate")
                          -- The shape of the upstream will be pure numbers, no 'All' business:
                          (All,  indA,_indF) -> mkPrj indA 1 upDims (getSizeE upV) (error "ExplicitShapes: Replicate")
                      | pr <- fromJust $ fragileZip3 template indsA indsF ]
                 -- Sum up the number of Alls seen so far to get the index into the original shape:
                 indsA = tail$reverse$scanl (\ ind x -> if x==All   then ind+1 else ind) 0 (reverse template)
                 indsF = tail$reverse$scanl (\ ind x -> if x==Fixed then ind+1 else ind) 0 (reverse template)
             ex' <- doE ex   -- The new shape template.
             -- Here we produce both a shape
             return ([ProgBind gensym exTy UnknownSize (Left ex')],
                     mkETuple ls, 
                     Replicate template (EVr gensym) upV)

        -- Later we can optimize the trivial case of all All's if we like:
        Index template vr ex   ->
          do 
             let 
                 numAlls = length$ filter (==All) template
                 -- The number of remaining dimensions in the shape will be the number of All's
                 ls = [ mkPrj i 1 numAlls (getSizeE vr) (error "ExplicitShapes: Index")
                      | i <- indsF]
                 -- Get the index of the All entries within the original, pre-knockout shape:
                 loop []          = []
                 loop (Fixed:rst) = map (+1) $ loop rst
                 loop (All  :rst) = 0 : loop rst
                 indsF = reverse$ loop$ reverse template
             ex' <- doE ex 
             return ([], mkETuple ls, Index template vr ex')

        -- Cannot handle Scanl' because of it's tuple return type.  It's not really an "array variable":
        Scanl'   _ _ _     -> error$ "ExplicitShapes: cannot handle Scanl' because of its tuple return type"
        Scanr'   _ _ _     -> error$ "ExplicitShapes: cannot handle Scanr' because of its tuple return type"
        Use      _         -> error$"ExplicitShapes: it should not be possible to find a Use with Unknown size: "++ show vo
        Use'     _ _ _     -> error$"ExplicitShapes: it should not be possible to find a Use' with Unknown size: "++ show vo        
        Unit     _         -> error$"ExplicitShapes: it should not be possible to find a Unit with Unknown size: "++ show vo
      ) -- End handleUnknownSize

doE :: Exp -> MyM Exp
doE ex = do
  prog <- ask
  case ex of
    -- Here's the important bit:
    EShape avr  -> return$ mkSizeE prog avr

    -- EShapeSize (EShape vr) -> -- We can optimize this in the future if we like.
    EShapeSize ex1 ->
         case topLevelExpType prog ex1 of
           TInt      -> doE ex1
           TTuple [] -> return$ EConst (I 0)
           TTuple ls -> do tmp <- lift $ genUniqueWith "eshpsz"
                           ex2 <- doE ex1
                           let ndims = length ls
                           maybtrace (" TEMPMSG[ExplicitShapes] ESHAPESIZE of "++ show ex1 ++" - we think it has ndims = "++show ndims) $ return() 
                           return$ 
                             ELet (tmp, TTuple ls, ex2) $
                              foldl (\ acc i -> mulI acc (mkPrj i 1 ndims (EVr tmp) TInt))
                                    (EConst (I 1))
                                    (reverse [0..ndims - 1])
           ty -> error$"invariant broken: bad type for shape tuple: "++show ty

    -- Boilerplate:     
    ----------------------------------------
    EVr _               -> return ex
    EConst _            -> return ex
    ECond e1 e2 e3      -> ECond  <$> doE e1 <*> doE e2 <*> doE e3
    EWhile (Lam1 a1 bod1) (Lam1 a2 bod2) e3 -> EWhile <$> (Lam1 a1 <$> doE bod1)
                                                      <*> (Lam1 a2 <$> doE bod2)
                                                      <*> doE e3  
  
    ELet (v,t,rhs) bod  -> (\r b -> ELet (v,t,r) b) <$> doE rhs <*> doE bod
    ETupProject t i l e -> ETupProject t i l <$> doE e
    EPrimApp p t els    -> EPrimApp    p t   <$> mapM doE els
    ETuple els          -> ETuple            <$> mapM doE els
    EIndexScalar avr e  -> EIndexScalar avr  <$> doE e
    EIndex _            -> doerr ex
  where
    rfn1 (Lam1 (v,t) e ) = Lam1 (v,t) $ doE e 
       
-- | This handles the boring case where we are NOT adding a `_shape` binding.
doAE :: AExp -> MyM AExp
doAE ae =
  case ae of
    -- Reshape is eliminated here; it is a shape-only operation:
    Reshape _shE v                    -> return (Vr v)
    
    -- EVERYTHING BELOW IS BOILERPLATE:
    ------------------------------------------------------------
    Use _                             -> return ae
    Use' _ _ _                        -> return ae
    Vr _                              -> return ae
    Unit ex                           -> Unit <$> doE ex
    Cond a b c                        -> Cond <$> doE a <*> return b <*> return c
    Generate e (Lam1 arg bod)         -> Generate <$> doE e <*> (Lam1 arg <$> doE bod)
    Map      (Lam1 arg bod) vr        -> Map  <$> (Lam1 arg <$> doE bod) <*> return vr
    ZipWith  (Lam2 a1 a2 bod) v1 v2   -> ZipWith <$> (Lam2 a1 a2 <$> doE bod) <*> return v1 <*> return v2
    Backpermute ex (Lam1 arg bod) vr  -> Backpermute <$> doE ex <*> (Lam1 arg <$> doE bod)  <*> return vr
    Replicate template ex vr          -> Replicate template <$> doE ex <*> return vr
    Index slc vr ex                   -> Index slc vr <$> doE ex

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

doerr :: Out a => a -> t
doerr e = error$ "ExplicitShapes: the following should be desugared before this pass is called:\n   "++ show (doc e)

-- | Create an expression representing the size of array avr.  This depends on
-- whether or not the shape is known.
mkSizeE :: Prog ArraySizeEstimate -> Var -> Exp
mkSizeE prog avr = 
  let (Just(ProgBind _ _ dec _)) = lookupProgBind avr (progBinds prog) in
  case dec of
    KnownSize ls -> mkIndExp ls
    UnknownSize  -> EVr (shapeName avr)

mkPrj2 :: Int -> Int -> Int -> Exp -> Exp
mkPrj2 a b c d = error$ "mkPrj2: "++show(a,b,c,d)
