{-# LANGUAGE NamedFieldPuns #-}

-- | This module defines a compiler pass for removing the `Unit` construct.
module Data.Array.Accelerate.BackendKit.Passes.DesugarUnit (desugarUnit) where 
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc

desugarUnit :: Prog a -> Prog a 
desugarUnit prog@Prog{progBinds} =
  prog { progBinds= map doBind progBinds}

doBind :: ProgBind a -> ProgBind a 
doBind x@(ProgBind _ _  _ (Left _)) = x
doBind orig@(ProgBind vr ty dec (Right ae)) = 
  case ae of 
    Unit ex -> ProgBind vr ty dec
               (Right (Generate (ETuple [])
                       (Lam1 (var "indUnit", TTuple []) ex)))
    oth -> orig


-- | A test oracle. Verify that the compiler pass above did its job.
verifyNoUnit :: Prog a -> Prog a -> Bool
verifyNoUnit _orig Prog{progBinds} = not (or (map isUnit progBinds))
  where
    isUnit (ProgBind _ _ _ (Right (Unit _))) = True
    isUnit _                    = False


