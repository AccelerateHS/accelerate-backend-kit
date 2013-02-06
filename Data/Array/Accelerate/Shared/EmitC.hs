{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module contains a specialization of the generic code
-- emission structure in "Data.Array.Accelerate.Shared.EmitCommon".
-- It emits code meant for ICC.
--
-- Unfortunately, this arrangement currently requires careful
-- management of invariants that are NOT reflected in the type system.
-- See `emitC` below and `emitOpenCL` for details.

module Data.Array.Accelerate.Shared.EmitC
       (emitC, ParMode(..)) where

import           Control.Monad (forM_, when)
import           Data.List as L
import qualified Data.Map  as M
import qualified Prelude   as P
import Prelude (($), show, error, return, mapM_, String, fromIntegral, Int)
import Text.PrettyPrint.HughesPJ       (text)
import Text.PrettyPrint.GenericPretty (Out(doc))
import Debug.Trace (trace)

import Data.Array.Accelerate.Shared.EasyEmit as E
import Data.Array.Accelerate.Shared.EmitHelpers (builderName, emitCType, fragileZip)
import Data.Array.Accelerate.Shared.EmitCommon
import Data.Array.Accelerate.BackendKit.IRs.Metadata  (ArraySizeEstimate(..), FreeVars(..))
import Data.Array.Accelerate.BackendKit.IRs.GPUIR as G
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..), Var, AccArray(arrDim))
import Data.Array.Accelerate.BackendKit.CompilerUtils (dbg)




-- | Here is a new type just to create a new instance and implement the type class methods:
--   We also keep around an environment that we extract from the top level program.
data CEmitter = CEmitter ParMode Env
data ParMode = CilkParallel | Sequential
type Env = M.Map Var Type

-- | The final pass in a compiler pipeline.  It emit a GPUProg as a C
-- program meant for ICC (the Intel C Compiler).
-- 
-- This does not handle the full GPUProg grammar, rather it requires
-- that there be no SSynchronizeThreads or EGetLocalID / EGetGlobalID
-- constructs.
emitC :: ParMode -> GPUProg (ArraySizeEstimate,FreeVars) -> String
emitC pm prog@GPUProg{progBinds} =
    emitGeneric (CEmitter pm (M.fromList binds)) prog
  where
    binds = L.map (\(v,_,ty) -> (v,ty)) $
            concatMap outarrs progBinds

-- | We fill in the plain-C-specific code generation methods:
instance EmitBackend CEmitter where
  emitIncludes _ = do 
    include "stdlib.h"
    include "stdio.h"
    include "stdint.h"
    include "stdbool.h"
  
  invokeKern (CEmitter CilkParallel _) len body = E.cilkForRange (0,len) body
  invokeKern (CEmitter Sequential _)   len body = E.forRange (0,len) body

  emitType _ = emitCType

  emitMain e prog@GPUProg{progBinds} = do 
    _ <- funDef "int" "main" [] $ \ () -> do
           comm "First we EXECUTE the program by executing each array op in order:"
           mapM_ (execBind e prog) (L.zip [0..] progBinds)
           comm "This code prints the final result(s):"
           forM_ (progResults prog) $ \ result -> 
             printArray e result (lkup result progBinds)
           return_ 0
    return ()

  -- ARGUMENT PROTOCOL: Folds expect: ( inSize, inStride, outArrayPtr, inArrayPtr, initElems..., kernfreevars...)
  emitFoldDef e@(CEmitter _ env) (GPUProgBind{ evtid, outarrs, decor=(_,FreeVars arrayOpFVs), op }) = do
    let Fold (Lam formals bod) initEs inV _ = op
        vs = take (length initEs) formals
        ws = drop (length initEs) formals
        initargs = map (\(vr,_,ty) -> (emitType e ty, show vr)) vs
        [(outV,_,outTy)] = outarrs 
        outarg   = (emitType e outTy, show outV)
        inarg    = (emitType e (env M.! inV), show inV)
        freeargs = zip [error "FINISHME5 - EmitC.hs: Need types for free vars"] (map show arrayOpFVs)
        int_t = emitType e TInt
    
    _ <- rawFunDef "void" (builderName evtid) ((int_t, "inSize") : (int_t, "inStride") : 
                                               outarg : inarg : initargs ++ freeargs) $ 
         do E.forStridedRange (0, "inStride", "inSize") $ \ ix -> do 
              let [(wvr, _, wty)] = ws in 
      --        forM_ ws $ \ (wvr, _, wty) -> 
                varinit (emitType e wty) (varSyn wvr) (arrsub (varSyn inV) ix)
              tmps <- emitBlock e bod
              eprintf " ** Folding in position %d (it was %d) intermediate result %d\n"
                      [ix, (arrsub (varSyn inV) ix), varSyn$ head tmps]
              forM_ (fragileZip tmps vs) $ \ (tmp,(v,_,_)) -> set (varSyn v) (varSyn tmp)
              return ()
            arrset (varSyn outV) 0 (varSyn$ fst3$ head vs) 
            return () -- End rawFunDef
    return () -- End emitFoldDef
   

--------------------------------------------------------------------------------

-- | Generate code that will actually execute a binding, creating the
--    array in memory.  This is typically called to build the main() function.
execBind :: (EmitBackend e) => e 
             -> GPUProg (ArraySizeEstimate,FreeVars)
             -> (Int, GPUProgBind (ArraySizeEstimate,FreeVars))
             -> EasyEmit ()
execBind e _prog (_ind, GPUProgBind {outarrs=resultBinds, op=(ScalarCode blk)}) = do
   -- Declare and then populate then populate the scalar bindings:
   forM_ resultBinds $ \ (vr,_,ty) ->
     var (emitType e ty) (varSyn vr)
   E.block $ do 
      results <- emitBlock e blk
      forM_ (zip resultBinds results) $ \ ((vr,_,_),res) ->
        set (varSyn vr) (varSyn res)

   when dbg$ forM_ resultBinds $ \ (vr,_,ty) -> do
     eprintf (" [dbg] Top lvl scalar binding: "++show vr++" = "++ printfFlag ty++"\n") [varSyn vr]
   return ()
     
execBind e _prog (_ind, GPUProgBind {evtid, outarrs, op, decor=(_,FreeVars arrayOpFVs)}) =
  let [(outV,_,ty)] = outarrs -- FIXME -- only handling one-output arrays for now...
      TArray _ elty = ty 
      elty' = emitType e elty in
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
      let len   = emitE e numelems
      varinit (emitType e ty) (varSyn outV) (function "malloc" [sizeof elty' * len])
      return ()
  
    Kernel dimSzs (Lam formals _) args -> do
      -- The builder function also needs any free variables in the size:
      let [(_,szE)] = dimSzs
          sizearg = 
            case szE of
              EConst (I n) -> [fromIntegral n]
              EVr v        -> [varSyn v]
      -- Call the builder to fill in the array: 
      emitStmt$ (function$ strToSyn$ builderName evtid) (sizearg ++ map (emitE e) args)
      return ()

    -- TODO: Should we keep just Kernel or just Generate or both?
    Generate els (Lam pls bod) -> do
      error$"EmitC.hs/execBind: We don't directly support Generate kernels, they should have been desugared."

    -- This is unpleasantly repetetive.  It doesn't benefit from the lowering to expose freevars and use NewArray.
    Fold (Lam [(v,_,ty1),(w,_,ty2)] bod) [initE] inV (ConstantStride (EConst (I stride))) -> do
      -- The builder function also needs any free variables in the size:
      let freevars = arrayOpFVs 
          initarg = 
            case initE of
              EConst (I n) -> fromIntegral n
              EVr v        -> varSyn v
          len = 1  -- Output is fully folded
          insize  = trace "FINISHME3 EmitC.hs -- need size in Fold, hardcoding... " 10
          allargs = insize : fromIntegral stride : varSyn outV : varSyn inV : initarg : map varSyn freevars
          
      varinit (emitType e ty) (varSyn outV) (function "malloc" [sizeof elty' * len])
      -- Call the builder to fill in the array: 
      emitStmt$ (function$ strToSyn$ builderName evtid) allargs
      return ()
            
    Scan (Lam pls bod) dir els inV -> do
      error$"EmitC.hs/execBind: FINISHME - Scan case "
--    _ -> error$"EmitC.hs/execBind: can't handle this array operator yet: "++show op


--------------------------------------------------------------------------------
-- | Generate code to print out a single array of known size.
--   Takes as input the ProgBind that produced the array.
printArray :: (Out a, EmitBackend e) => e -> Var -> GPUProgBind a -> EasyEmit ()
printArray e name (GPUProgBind { outarrs=[(vr,_,(TArray ndims elt))], op}) = do
  len <- tmpvar (emitType e TInt)
  let szE = case op of
             NewArray s -> s
             Use arr    -> EConst$ I$ product$ arrDim arr
             -- FIXME: For now we punt and don't print anything:
             Cond _ _ _   -> trace ("Warning: finish Cond case in printArray")$ 
                             EConst (I 0)
             -- A full fold:
             Fold _ _ _ (ConstantStride (EConst (I 1))) -> EConst (I 1)
             oth -> error$"EmitC.hs/printArray, huh, why are we printing the result of this op?: "++show oth
  case ndims of
     1 -> case szE of 
            EConst (I n) -> set len (fromIntegral n)
            EVr v        -> set len (varSyn v)
     0  -> set len "1"
     oth -> error$"printArray: not yet able to handle arrays of rank: "++ show oth
  printf " [ " []
  printit 0  
  for 1 (E.< len) (+1) $ \ind -> do
     printf ", " []
     printit ind
  printf " ] " []
  where     
    printit ind = printf (printfFlag elt) [arrsub (varSyn vr) ind]

-- printArray oth = error$ "Can only print arrays of known size currently, not this: "++show (fmap fst oth)
printArray _ _ oth = error$ "EmitC.hs/printArray: Bad progbind:"++show (doc oth)


--------------------------------------------------------------------------------  
-- Helpers and Junk
--------------------------------------------------------------------------------

include :: String -> EasyEmit ()
include str = emitLine$ toSyntax$ text$ "#include \""++str++"\""

fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a

thd3 :: (t, t1, t2) -> t2
thd3 (_,_,c) = c
