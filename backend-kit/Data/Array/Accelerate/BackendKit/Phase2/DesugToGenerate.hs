{-# LANGUAGE NamedFieldPuns #-}

-- | This module exports a pass which desugars Map, ZipWith, and Backpermute to Generate.

module Data.Array.Accelerate.BackendKit.Phase2.DesugToGenerate (desugToGenerate) where

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
import Data.Array.Accelerate.BackendKit.IRs.Metadata (Uses(..), ArraySizeEstimate(..))
import Data.Array.Accelerate.BackendKit.Utils.Helpers (shapeName)
import qualified Data.Map as M
import Debug.Trace

-- | This pass corrupts the `Uses` counts and therefore removes that
--   annotation.
desugToGenerate :: Prog (ArraySizeEstimate,Uses) -> Prog (ArraySizeEstimate)
desugToGenerate prog@Prog{progBinds} =
   prog { progBinds= doBinds 2000 M.empty progBinds }


-- | This keeps a map of known sizes as it walks the progbinds:
doBinds :: Int -> (M.Map Var [Int]) -> [ProgBind (ArraySizeEstimate,Uses)] -> [ProgBind (ArraySizeEstimate)]
-- Do nothing to scalar binds:
doBinds _ _ [] = []
doBinds n mp (pb@(ProgBind _ _ _ (Left _)) : rest)    = fmap fst pb : doBinds (n+1) mp rest
doBinds n mp (ProgBind arOut ty (size, _) (Right ae) : rest) = this : doBinds (n+1) mp' rest 
 where
   mp' = case size of 
           UnknownSize -> mp
           KnownSize ls -> M.insert arOut ls mp
   this = 
     -- The output array is the same size and type, but generated in a different way:
     ProgBind arOut ty size $ Right $ 
     case ae of 
       Map (Lam1 (evr, ety) bod) arIn ->
         Generate theshape
          (Lam1 (ind, indty)
           (ELet (evr, ety, EIndexScalar arIn (EVr ind))
                 bod))

       ZipWith (Lam2 (evr1, ety1) (evr2, ety2) bod) arIn1 arIn2 ->
         Generate theshape
          (Lam1 (ind, indty)
           (ELet (evr1,ety1, EIndexScalar arIn1 (EVr ind)) $
            ELet (evr2,ety2, EIndexScalar arIn2 (EVr ind)) $ 
                 bod))
         
       -- This one is trivial:
       Backpermute esz (Lam1 (ind, indty) bod) arIn -> 
         Generate esz          
            (Lam1 (ind, indty) (EIndexScalar arIn bod))
         
       oth -> oth -- Other AExps are unchanged.

   ind = var$"indG_"++show n
   indty = case ty of
            TArray n _ -> mkTTuple$ replicate n TInt

   theshape :: Exp
   theshape = 
     case size of               
       KnownSize ls -> mkETuple $ map (EConst . I) ls 
       -- Any unknown-sized arrays will have explicit variables tracking their shape at this point:
       UnknownSize  -> EVr (shapeName arOut)

-- TODO FIXME: Handle unknown sizes and intersections:
createShapeIntersection :: Int -> [Either Var [Int]] -> [Exp]
createShapeIntersection = error "FINISHME: DesugToGenerate.hs: createShapeIntersection"
  -- This needs to either use the information we have statically, or
  -- use EShape to get the necessary information at runtime.
