{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Array.Accelerate.Shared.EmitC
       (emitC) where

import Text.PrettyPrint.HughesPJ       (text)
import Data.List as L
import Control.Monad                   (forM_)
import Data.Array.Accelerate.Shared.EasyEmit as E
import Prelude as P

import Data.Array.Accelerate.Shared.EmitHelpers (builderName, emitCType)
import Data.Array.Accelerate.Shared.EmitCommon 
import Data.Array.Accelerate.BackendKit.IRs.GPUIR as G
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..), Var, AccArray(arrDim))


-- | Here is a new type just to create a new instance and implement the type class methods:
data CEmitter = CEmitter

-- emitC :: LLProg (ArraySizeEstimate,FreeVars) -> String
emitC :: GPUProg () -> String
emitC = emitGeneric CEmitter 

-- | We fill in the plain-C-specific code generation methods:
instance EmitBackend CEmitter where
  emitIncludes _ = do 
    include "stdlib.h"
    include "stdio.h"
    include "stdint.h"
    include "stdbool.h"
  
  invokeKern e len body = -- (aty,arrlen)
     forRange (0,len) body

  emitType _ = emitCType

  emitMain e prog@GPUProg{progBinds} = do 
    funDef "int" "main" [] $ \ () -> do
      comm "First we EXECUTE the program by executing each array op in order:"
      mapM_ (execBind e prog) (L.zip [0..] progBinds)
      comm "This code prints the final result(s):"
      forM_ (progResults prog) $ \ result -> 
        printArray e result (lkup result progBinds)
      return_ 0
    return ()


-- | Generate code that will actually execute a binding, creating the
--    array in memory.  This is typically called to build the main() function.
execBind :: EmitBackend e => e 
             -> GPUProg () 
             -> (Int, GPUProgBind ()) 
             -> EasyEmit ()
execBind e _prog (_ind, GPUProgBind {outarrs=resultBinds, op=(ScalarCode blk)}) = do
   -- Declare and then populate then populte the scalar bindings:
   forM_ resultBinds $ \ (vr,_,ty) ->
     var (emitType e ty) (varSyn vr)
   E.block $ do 
      results <- emitBlock e blk
      forM_ (zip resultBinds results) $ \ ((vr,_,_),res) ->
        set (varSyn vr) (varSyn res)
   return ()
     
execBind e _prog (_ind, GPUProgBind {evtid, outarrs, op}) =
  let [(outV,_,ty)] = outarrs in -- FIXME -- only handling one-output arrays for now...
  case op of 
    -- In the case of array conditionals we need to run the scalar
    -- code, then assign the result accordingly.  TODO: this is a
    -- broken kind of eager evaluation currently.  It executes EVERYTHING:
    Cond etest bvr cvr -> do 
      comm "Declare an array (pointer) that will be set based on a conditional:"
      E.var (emitType e ty) (varSyn outV)
      if_ (emitE e etest)
        (set (varSyn outV) (varSyn bvr))
        (set (varSyn outV) (varSyn cvr))

    NewArray numelems -> do
      let TArray _ elty = ty
          elty' = emitType e elty
          len   = emitE e numelems
      varinit (emitType e ty) (varSyn outV) (function "malloc" [sizeof elty' * len])
      
      return ()
  
    Kernel dimSzs (Lam formals _) args -> do
      let [(_,szE)] = dimSzs
          sizefree = -- map undefined (S.toList (expFreeVars szE))
            case szE of
              EConst (I n) -> [fromIntegral n]
              EVr v    -> [varSyn v]
      -- Call the builder to fill in the array: 
      emitStmt$ (function$ strToSyn$ builderName evtid) (sizefree ++ map (emitE e) args)
      return ()

    _ -> error$"EmitC.hs/execBind: can't handle this array operator yet: "++show op


-- | Generate code to print out a single array of known size.
--   Takes as input the ProgBind that produced the array.
printArray :: EmitBackend e => e -> Var -> GPUProgBind () -> EasyEmit ()
printArray e name (GPUProgBind { outarrs=[(vr,_,(TArray ndims elt))], op}) = do
  len <- tmpvar (emitType e TInt)
  let szE = case op of
             NewArray szE -> szE
             Use arr    -> EConst$ I$ product$ arrDim arr
             -- FIXME: For now we punt and don't print anything:
             Cond _ _ _ -> EConst (I 0)
             oth -> error$"EmitC.hs/printArray, huh, why are we printing the result of this op?: "++show oth
  case ndims of
     1 -> case szE of 
            EConst (I n) -> set len (fromIntegral n)
            EVr v        -> set len (varSyn v)
     0  -> set len "1"
     oth -> error$"printArray: not yet able to handle arrays of shape: "++ show oth
  for 0 (E.< len) (+1) $ \ind -> do 
     printit ind  
  where     
    printit ind = emitStmt (printf [stringconst$show name++"[%d] = "++ printfFlag elt ++"\n",
                          ind,
                          arrsub (varSyn vr) ind
                         ])

-- printArray oth = error$ "Can only print arrays of known size currently, not this: "++show (fmap fst oth)
printArray _ _ oth = error$ "EmitC.hs/printArray: Bad progbind:"++show oth


--------------------------------------------------------------------------------  
-- Helpers and Junk
--------------------------------------------------------------------------------

include :: String -> EasyEmit ()
include str = emitLine$ toSyntax$ text$ "#include \""++str++"\""
