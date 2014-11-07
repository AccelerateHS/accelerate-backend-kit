{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Array.Accelerate.BackendKit.Phase2.SizeAnalysis (sizeAnalysis, ArraySizeEstimate(..)) where 

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.List as L
import Data.Map  as M
import Data.Array.Accelerate.BackendKit.IRs.Metadata (ArraySizeEstimate(..))
import Debug.Trace 

sizeAnalysis :: Prog () -> Prog ArraySizeEstimate
sizeAnalysis prog@Prog{progBinds} =
  prog { progBinds= doBinds M.empty progBinds }

-- This function processes a list of topologically sorted (def before use) bindings.
-- The accumulator (Map) argument tracks sizes discovered so far (but only KNOWN sizes).
doBinds :: (M.Map Var [Int]) -> [ProgBind a] -> [ProgBind ArraySizeEstimate]
doBinds _ [] = []
doBinds mp (ProgBind vr ty  _ rhs : rest) =
  let sz = case rhs of
                  Right ae -> doAE mp ae 
                  Left ex  -> doE  mp ex -- These don't HAVE sizes, they ARE size descriptors.
      newMp = case sz of
               UnknownSize    -> mp  -- No new information.
               KnownSize ints -> M.insert vr ints mp
  in ProgBind vr ty sz rhs : doBinds newMp rest

-- Given information on already-bound arrays, what is the size of a particular AExp.
doAE :: (M.Map Var [Int]) -> AExp -> ArraySizeEstimate
doAE mp ae =
  case ae of
    -- CASE 0: Trivial:
    --------------------------------------------
    -- This is an easy one!  We have the array, thus we know it's size:
    Use arr -> KnownSize (arrDim arr)

    -- This is a hack. We might or might not know the exact size of this array.
    -- What's the worst that will happen if we pretend we never know?
    Use' _ -> UnknownSize

    -- CASE 1: Derivative arrays, look upstream:
    --------------------------------------------
    Vr v             -> useSizeof v
    -- Map creates a result the same size as its input.
    Map    _ vr      -> useSizeof vr
    -- We know what effect fold has on dimensionality.  It collapses
    -- the inner dimension...
    Fold _ _ vr      -> collapseInner vr
    Fold1  _ vr      -> collapseInner vr
    FoldSeg _ _ vr w -> replaceInner (useSizeof vr) (useSizeof w)
    Fold1Seg  _ vr w -> replaceInner (useSizeof vr) (useSizeof w)
    Scanl  _ _  vr   -> incrementInner vr -- useSizeof vr  
-- Not handling these yet because of their tuple return type:
--    Scanl' _ _  vr   -> useSizeof vr
    Scanl1 _    vr   -> useSizeof vr
    Scanr  _ _  vr   -> incrementInner vr -- useSizeof vr
--    Scanr' _ _  vr   -> useSizeof vr
    Scanr1 _    vr   -> useSizeof vr
    Permute _ vr _ _ -> useSizeof vr
    Stencil _ _ vr   -> useSizeof vr
    Stencil2 _ _ v1 _ v2 -> intersectVars v1 v2

    -- ZipWith takes the INTERSECTION of two extents.
    -- TODO: if we don't know BOTH we can issue smaller than constraints.
    ZipWith _ v1 v2 -> intersectVars v1 v2

    -- If both branches yield known sizes, and they're the same, then we
    -- record the size of the output:
    Cond _ v1 v2 ->
      case (M.lookup v1 mp, M.lookup v2 mp) of
        (Just sz1, Just sz2) | sz1 == sz2 -> KnownSize sz1
        _ -> UnknownSize

    -- CASE 2: Examine scalar Exps to determine size:
    -------------------------------------------------
    Generate e _      -> doE mp e
    Reshape e _       -> doE mp e
    Backpermute e _ _ -> doE mp e
    Replicate template e v ->
      -- trace ("Sizing Replicate "++ show (template, e, v, mp)) $ 
      case M.lookup v mp of 
        Nothing -> UnknownSize
        Just ls -> doEWith template ls mp e      

    -- Special case: if we cut down to zero dimensions then we know the size!
    Index template _ _ | all (==Fixed) template -> KnownSize []
    Index template vr ex ->
      case M.lookup vr mp of
        Nothing -> UnknownSize
        Just ls -> KnownSize $
                   L.map snd $
                   L.filter ((==All) . fst) $
                   L.zip template ls

    Unit _ -> error "sizeAnalysis: Unit is not part of the grammar accepted by this pass"
    oth    -> error $ "sizeAnalysis: not expecting this: "++(take 500$ show oth)
 where
   useSizeof vr =
     case M.lookup vr mp of
        Nothing -> UnknownSize
        Just sz -> KnownSize sz
   collapseInner vr =
     case M.lookup vr mp of
        Nothing -> UnknownSize
        Just (_:tl) -> KnownSize tl
   --BJS + MV:  For Scan !  
   incrementInner vr =
     case M.lookup vr mp of
        Nothing -> UnknownSize
        Just (h:tl) -> KnownSize $ h+1:tl 

   replaceInner _ UnknownSize = UnknownSize
   replaceInner UnknownSize _ = UnknownSize
   replaceInner (KnownSize (_:tl)) (KnownSize [inn]) = KnownSize (inn:tl)
   replaceInner x y = error$"SizeAnalysis/replaceInner: bad inputs: "++show(x,y)

   intersectVars v1 v2 = 
      case (M.lookup v1 mp, M.lookup v2 mp) of
        (Just sz1, Just sz2) -> KnownSize (intersectShapes sz1 sz2)
        _ -> UnknownSize

-- | IntersectShapesion of two shapes.
intersectShapes :: [Int] -> [Int] -> [Int]
intersectShapes sh1 sh2 | length sh1 == length sh2 = zipWith min sh1 sh2
intersectShapes sh1 sh2 = error$"intersectShapes: different rank shapes: " ++ show (sh1,sh2)


-- | Scalar expressions are used to encode shapes in several places.
--   Here we try to STATICALLY EVALUATE such expressions to retrieve a shape.
doE :: (M.Map Var [Int]) -> Exp -> ArraySizeEstimate
doE mp ex = -- doEWith (repeat Fixed) []
  -- (\x -> trace ("[SizeAnalysis] attempting static evaluation of "++show ex++", size map "++ show mp++ " -> "++show x) x) $ 
  case normalizeEConst ex of
    ETuple []                       -> KnownSize [] -- SCALAR!

    -- Unit values (such as in replicate slices) are IGNORED here:
--    ETuple (ETuple [] : rest)       -> doE mp (ETuple rest)
    
    EConst len |     isIntConst len -> KnownSize [constToNum len]
               |     otherwise      -> UnknownSize
    ETuple ls -> doEs mp ls 

-- all isShapeConst ls -> KnownSize (L.map (constToNum . unEConst) (L.filter (not . isUnit) ls))
--                |     otherwise      -> UnknownSize

    -- The following should be common.  Base the shape on the shape of a different array:
    EShape vr -> case M.lookup vr mp of
                   Nothing -> UnknownSize
                   Just ls -> KnownSize ls

    EShapeSize ex -> 
      case doE mp ex of
        KnownSize ls -> KnownSize [sum ls]
        UnknownSize  -> UnknownSize

    ETupProject ind len tup -> 
      -- Here we try to press on.  This is silly but it could happen:
      case doE mp tup of 
        UnknownSize  -> UnknownSize
        KnownSize ls -> KnownSize$ reverse$ take len$ drop ind$ reverse ls

    EIndexScalar _ _  -> UnknownSize -- In general, unknowable.
    ELet _ _          -> UnknownSize -- We could do more work on this, but won't.
    EPrimApp _ _ _    -> UnknownSize -- The prog could do some arithmetic to compute a size...
    ECond _ _ _       -> UnknownSize
    EWhile _ _ _      -> UnknownSize 
    -- This one won't happen because top-level varrefs are ONLY
    -- created by us (and that's for boolean bindings for array level
    -- conditionals only):
    EVr vr -> error$ "SizeAnalysis: this case should be impossible.  We should never use a top-level scalar variable for a shape: "++show vr   
    EIndex _          -> error "SizeAnalysis: this shouldn't happen (EIndex) because of normalizeEConst"


-- TEMP: This is a partial solution... we need to integrate with the interpreter and
-- make this a full simplifier pass.
doEs :: (M.Map Var [Int]) -> [Exp] -> ArraySizeEstimate
doEs mp [] = KnownSize []
doEs mp (hd:tl) = 
  case doEs mp tl of 
    UnknownSize -> UnknownSize 
    KnownSize ls2 -> 
      case doE mp hd of
        UnknownSize   -> UnknownSize
        KnownSize ls1 -> KnownSize $ ls1 ++ ls2

isShapeConst (ETuple []) = True
isShapeConst e = isIntEConst e 

isUnit (ETuple []) = True
isUnit _ = False

-- | This is the "full version" that accepts a template to know where to fill in "All" holes.
doEWith :: SliceType -> [Int] -> (M.Map Var [Int]) -> Exp -> ArraySizeEstimate
doEWith template oldSzs mp ex =   
  -- trace ("[SizeAnalysis] sizing expression "++show ex++" against slice template "++show (template,oldSzs)++", map "++ show mp) $ 
  case doE mp ex of 
    KnownSize ls -> KnownSize$ injectDims oldSzs template ls
    UnknownSize  -> UnknownSize
  where 
    -- Interleave "Fixed" and "All" lists of dimensions.
    injectDims :: [Int] -- ^ "All" Dimensions
               -> SliceType 
               -> [Int] -- ^ "Fixed" dimensions.
               -> [Int]
    injectDims [] [] [] = []
    injectDims (dim:l1) (All : l2)    l3       = dim : injectDims l1 l2 l3
    injectDims l1       (Fixed : l2)  (dim:l3) = dim : injectDims l1 l2 l3
    injectDims l1 l2 l3 = error$ "SizeAnalysis/injectDims: bad input: "++ show (l1,l2,l3)

isIntEConst :: Exp -> Bool
isIntEConst (EConst c) = isIntConst c
isIntEConst _          = False

unEConst :: Exp -> Const
unEConst (EConst x) = x
unEConst x          = error$"unEConst: expected EConst, got "++show x
