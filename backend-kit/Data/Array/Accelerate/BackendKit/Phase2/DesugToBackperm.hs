{-# LANGUAGE NamedFieldPuns, CPP #-}

module Data.Array.Accelerate.BackendKit.Phase2.DesugToBackperm (desugToBackperm) where
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.IRs.Metadata  (Uses(Uses), ArraySizeEstimate(..))
import Data.Array.Accelerate.BackendKit.Utils.Helpers (mkIndTy,mkIndExp,maybtrace, shapeName)
import Debug.Trace
import Data.List as L

-- | This pass eliminates Replicate and Index(Slice) array operators.
desugToBackperm :: Prog (ArraySizeEstimate,Uses) -> Prog (ArraySizeEstimate,Uses)
desugToBackperm prog@Prog{progBinds} =
  prog{ progBinds= zipWith (doBind prog) [1000..] progBinds }


doBind :: Prog (ArraySizeEstimate,a) -> Int -> ProgBind (ArraySizeEstimate,a) -> ProgBind (ArraySizeEstimate,a)
-- This pass measures KERNEL free vars, these scalar expressions don't count:
doBind _    _   (ProgBind v t d (Left ex))       = ProgBind v t d (Left ex)
doBind prog num (ProgBind avr outty (outsz,d) (Right ae)) =   
  -- ProgBind v t (sz,d) (Right (doAE prog ind t sz ae))
  ProgBind avr outty (outsz,d) $ Right $
  let gensym = var$ "indBP_"++show num
#define EXPLICITSHAPES_BEFORE_DESUGTOBACKPERM
#ifdef EXPLICITSHAPES_BEFORE_DESUGTOBACKPERM
      -- The ExplicitShapes pass has already gone to a lot of work to
      -- compute the (dynamic) sizes of Replicate and Index's outputs.
      -- We reuse that rather than redoing it here:
      szE = case outsz of 
                  KnownSize ls -> mkIndExp ls
                  UnknownSize  -> EVr$ shapeName avr -- This will already have been created by ExplicitShapes
#else 
      szE = ....
#endif      
  in    
  case ae of

    -- More sophisticated Replicate-handling for when we can properly deal with tuples.
    Replicate template _newDims vr -> 
      let indty = mkIndTy ndims
          ndims = length template
      in Backpermute szE 
          (Lam1 (gensym,indty)$ 
           mkETuple $ map snd $ 
           filter ((==All) . fst) $ 
           reverse $
           zip (reverse template) 
               [ mkPrj i 1 ndims (EVr gensym) | i <- [0..] ]
          ) vr

    -- TODO/FIXME: ensure that all non-trivial expressions are lifted into top level bindings!!
    Index template vr ex ->
      let TArray dimsOut _ = outty
          -- The tuple representation passed in as 'ex' is odd:
          exShp = reverse$ zip [0..] $
                  dropWhile (==All) (reverse template)
          hopExInd 0 ((i,Fixed):t) = i
          hopExInd 0 (_:t)         = hopExInd 0 t
          hopExInd n ((i,Fixed):t) = hopExInd (n-1) t
          hopExInd n (_:t)         = hopExInd n t
      in
      maybtrace ("[*] shape expression used in Index = "++show exShp)$ 
      Backpermute szE
        (Lam1 (gensym, mkIndTy dimsOut) $
         mkETuple $ 
          map (\ (t,i) ->
                case t of
                  All   -> mkPrj i 1 (dimsOut) (EVr gensym)
                  -- This is very ugly business:
                  Fixed -> mkPrj (hopExInd i exShp) 1 (length exShp) ex 
              )
            (reverse$ fn (0,0) (reverse template))
        )
        vr
        where
          fn _ [] = []
          fn (n,m) (All  :rst) = (All  ,n) : fn (n+1,m) rst
          fn (n,m) (Fixed:rst) = (Fixed,m) : fn (n,m+1) rst

#ifdef EXPLICITSHAPES_BEFORE_DESUGTOBACKPERM
    Reshape _ _ -> error$"DesugToBackperm: Reshape should have been desugared before this:\n "++ show ae
#endif
    _ -> ae
    
 where
   add (EConst (I 0)) n = n
   add n (EConst (I 0)) = n
   add n m              = EPrimApp TInt (NP Add) [n,m]
   
   mul (EConst (I 1)) n = n
   mul n (EConst (I 1)) = n
   mul n m              = EPrimApp TInt (NP Mul) [n,m]

   quot n (EConst (I 1)) = n
   quot n m              = EPrimApp TInt (IP Quot) [n,m]


-- FIXME: Quadratic lookups here:
getSize :: Prog (ArraySizeEstimate,b) -> Var -> ArraySizeEstimate
getSize prog v = sz
  where 
    Just (ProgBind _ _ (sz,_) _) = L.find (\ (ProgBind w _ _ _) -> v==w) (progBinds prog)

-- FIXME: Quadratic lookups here:
getType :: Prog (ArraySizeEstimate,b) -> Var -> Type
getType prog v = ty
  where 
    Just (ProgBind _ ty _ _) = L.find (\ (ProgBind w _ _ _) -> v==w) (progBinds prog)



-- Safely make a projection, taking care not to project from a ONE
-- ELEMENT tuple (i.e. not a tuple):
mkPrj :: Int -> Int -> Int -> Exp -> Exp
mkPrj _ _ 1 e = e 
mkPrj ind len _total e = ETupProject (error "DesugToBackperm: mkPrj") ind len e 



-- | Interleave "Fixed" and "All" lists of dimensions.
injectDims :: Show a 
           => [a] -- ^ "All" entries
           -> SliceType 
           -> [a] -- ^ "Fixed" entries.
           -> [a]
injectDims [] [] [] = []
injectDims (dim:l1) (All : l2)    l3       = dim : injectDims l1 l2 l3
injectDims l1       (Fixed : l2)  (dim:l3) = dim : injectDims l1 l2 l3
injectDims l1 l2 l3 = error$ "injectDims: bad input: "++ show (l1,l2,l3)
