{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module contains a specialization of the generic code
-- emission structure in "Data.Array.Accelerate.Shared.EmitCommon".
-- It emits code meant for ICC.
--
-- Unfortunately, this arrangement currently requires careful
-- management of invariants that are NOT reflected in the type system.
-- See `emitC` below and `emitOpenCL` for details.

module Data.Array.Accelerate.Shared.EmitC
       (emitC, ParMode(..), getUseBinds, standardResultOrder) where

import           Control.Monad (forM_, when)
import           Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Prelude   as P
import Prelude (($), show, error, return, mapM_, String, fromIntegral, Int)
import Text.PrettyPrint.HughesPJ       (text)
import Text.PrettyPrint.GenericPretty (Out(doc))
import Debug.Trace (trace)

import Data.Array.Accelerate.Shared.EasyEmit as E
import Data.Array.Accelerate.Shared.EmitHelpers (builderName, emitCType, fragileZip, (#))
import Data.Array.Accelerate.Shared.EmitCommon
import Data.Array.Accelerate.BackendKit.IRs.Metadata  (FreeVars(..))
import Data.Array.Accelerate.BackendKit.IRs.GPUIR as G
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..), Var, AccArray(arrDim), TrivialExp(..))
import Data.Array.Accelerate.BackendKit.CompilerUtils (dbg)
--------------------------------------------------------------------------------

-- | Here is a new type just to create a new instance and implement the type class methods:
--   We also keep around an environment that we extract from the top level program.
data CEmitter = CEmitter ParMode Env
data ParMode = CilkParallel | Sequential
type Env = M.Map Var Type

--------------------------------------------------------------------------------

-- | The final pass in a compiler pipeline.  It emit a GPUProg as a C
-- program meant for ICC (the Intel C Compiler).
-- 
-- This does not handle the full GPUProg grammar, rather it requires
-- that there be no SSynchronizeThreads or EGetLocalID / EGetGlobalID
-- constructs.
emitC :: ParMode -> GPUProg (FreeVars) -> String
emitC pm prog@GPUProg{progBinds} =
    emitGeneric (CEmitter pm (M.fromList binds)) prog
  where
    binds = L.map (\(v,_,ty) -> (v,ty)) $
            concatMap outarrs progBinds

-- | Internal: The name of the arguments record with Use-imported arrays:
globalArgs :: String
globalArgs = "argsRec"

-- | Internal: 
globalResults :: String
globalResults = "resultsRec"

-- | Find only the Use-bindings among the `progBinds`.  This standardizes the ORDER
-- in which Use bindings are fed to the compiled program.
getUseBinds :: GPUProg a -> [(Var,Type,AccArray)]
getUseBinds GPUProg{progBinds} = concatMap fn progBinds
 where
   fn (GPUProgBind{ outarrs, op= Use arr }) =
     let [(vr,_,arrty)] = outarrs
     in [(vr,arrty,arr)]
   fn _ = []

-- | `progResults` is not a set, the same variable may be returned at different
-- locations in the output "tuple".  This makes it into a set and returns it in a
-- canonical order.
standardResultOrder :: [Var] -> [Var]
standardResultOrder vrs = S.toList $ S.fromList vrs


-- | We fill in the plain-C-specific code generation methods:
instance EmitBackend CEmitter where
  emitIncludes e = do 
    include "stdlib.h"
    include "stdio.h"
    include "stdint.h"
    include "stdbool.h"
    case e of
      CEmitter Sequential   _ -> return ()
      CEmitter CilkParallel _ -> do include "cilk/cilk.h"
                                    include "cilk/reducer.h"
      
  invokeKern (CEmitter CilkParallel _) len body = E.cilkForRange (0,len) body
  invokeKern (CEmitter Sequential _)   len body = E.forRange (0,len) body

  emitType _ = emitCType

  -- In Cilk we use a vectorized ("elemental") function:
  scalarKernelReturnType (CEmitter CilkParallel _) = "__declspec(vector) void"
  scalarKernelReturnType (CEmitter Sequential _)   = "void"

  emitMain e prog@GPUProg{progBinds, progResults, sizeEnv} = do

    let useBinds   = getUseBinds prog
        allResults = standardResultOrder progResults
    ----------------------------------------
    ------    Argument Initialization  -----
    cppStruct "ArgRecord" "" $ do
      comm "These are all the Use arrays gathered from the Acc computation:"
      forM_ useBinds $ \ (vr,arrty,_) -> 
        E.emitStmt$ (emitType e arrty) +++ " " +++ varSyn vr
    rawFunDef "struct ArgRecord*" "CreateArgRecord" [] $ do
      return_ "malloc(sizeof(struct ArgRecord))"
    funDef "void" "DestroyArgRecord" ["struct ArgRecord*"] $ \arg -> do
      E.emitStmt$ function "free" [arg]
    forM_ useBinds $ \ (vr,ty,_) -> 
      funDef "void" ("LoadArg_" ++ show vr) ["struct ArgRecord*", "int", emitType e ty] $ \ (args,size,ptr) -> do
        comm$ "In the future we could do something with the size argument."
        let _ = size::Syntax
        set (args `arrow` (varSyn vr)) ptr
        return ()
    ----------------------------------------
    --------    Results Retrieval   --------
    cppStruct "ResultRecord" "" $ do
      comm "These are all the progResults arrays output from the Acc computation: "
      forM_ allResults $ \ name -> do
        let elt = P.fst$ sizeEnv # name 
        E.var (emitType e (TArray 1 elt)) (varSyn name)
        E.var "int" (strToSyn (show name ++ "_size"))
        return ()
    rawFunDef "struct ResultRecord*" "CreateResultRecord" [] $ do
      return_ "malloc(sizeof(struct ResultRecord))"
    funDef "void" "DestroyResultRecord" ["struct ResultRecord*"] $ \arg -> do
      comm "In the CURRENT protocol, we free all results SIMULTANEOUSLY, here:"
      forM_ allResults $ \ name -> do
        E.emitStmt$ function "free" [arg `arrow` varSyn name]
      E.emitStmt$ function "free" [arg]
    forM_ allResults $ \ name -> do 
      let elt = P.fst $ sizeEnv#name
      funDef (emitType e (TArray 1 elt)) ("GetResult_" ++ show name) ["struct ResultRecord*"] $ \ results -> do
        return_ (results `arrow` (varSyn name))
      funDef "int" ("GetResultSize_" ++ show name) ["struct ResultRecord*"] $ \ results -> do
        return_ (results `arrow` (varSyn name +++ "_size"))
        
    ----------------------------------------
      
    _ <- rawFunDef "void" "MainProg" [("struct ArgRecord*",globalArgs), ("struct ResultRecord*",globalResults)] $ do    
           comm "First we EXECUTE the program by executing each array op in order:"
           mapM_ (execBind e prog) (L.zip [0..] progBinds)
#if 0
           comm "This code prints the final result(s):"
           forM_ allResults $ \ result -> 
             printArray e prog result (lkup result progBinds)
#else              
           comm "We write the final output to the results record:"
           forM_ allResults $ \ rname -> do 
             E.set (strToSyn globalResults `arrow` varSyn rname) (varSyn rname)
             E.set (strToSyn globalResults `arrow` (varSyn rname+++"_size")) $
               case sizeEnv # rname of 
                 (_, TrivVarref vr) -> (varSyn vr)
                 (_, TrivConst  n)  -> fromIntegral n
#endif             
--           return_ 0
    return ()

  -- ARGUMENT PROTOCOL: Folds expect: ( inSize, inStride, outArrayPtr, inArrayPtr, initElems..., kernfreevars...)
  emitGenReduceDef e@(CEmitter _ env) (GPUProgBind{ evtid, outarrs, decor=(FreeVars arrayOpFVs), op }) = do
    let GenReduce {reducer,generator,variant,stride} = op
        Fold initSB@(ScalarBlock _ initVs _) = variant
        Lam formals bod = reducer
        Manifest inVs = generator

        -- TEMPORARY restriction:
        [inV] = inVs
        
        vs = take (length initVs) formals
        ws = drop (length initVs) formals
        initargs = map (\(vr,_,ty) -> (emitType e ty, show vr)) vs
        [(outV,_,outTy)] = outarrs 
        outarg   = (emitType e outTy, show outV)
        inarg    = (emitType e (env # inV), show inV)
        freeargs = map (\fv -> (emitType e (env # fv), show fv))
                       arrayOpFVs
        int_t = emitType e TInt
    
    _ <- rawFunDef "void" (builderName evtid) ((int_t, "inSize") : (int_t, "inStride") : 
                                               outarg : inarg : initargs ++ freeargs) $ 
         do E.comm$"Fold loop, reduction variable(s): "++show vs
            E.forStridedRange (0, "inStride", "inSize") $ \ ix -> do
              let [(wvr, _, wty)] = ws
              varinit (emitType e wty) (varSyn wvr) (arrsub (varSyn inV) ix)
              tmps <- emitBlock e bod
              eprintf " ** Folding in position %d (it was %d) intermediate result %d\n"
                      [ix, (arrsub (varSyn inV) ix), varSyn$ head tmps]
              forM_ (fragileZip tmps vs) $ \ (tmp,(v,_,_)) ->
                 set (varSyn v) (varSyn tmp)
              return ()
            arrset (varSyn outV) 0 (varSyn$ fst3$ head vs) 
            return () -- End rawFunDef
    return () -- End emitFoldDef
   

--------------------------------------------------------------------------------

-- | Generate code that will actually execute a binding, creating the
--    array in memory.  This is typically called to build the main() function.
execBind :: (EmitBackend e) => e 
             -> GPUProg (FreeVars)
             -> (Int, GPUProgBind (FreeVars))
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
     
execBind e GPUProg{sizeEnv} (_ind, GPUProgBind {evtid, outarrs, op, decor=(FreeVars arrayOpFVs)}) =
  let [(outV,_,ty)] = outarrs -- FIXME -- only handling one-output arrays for now...
      TArray _ elty = ty 
      elty' = emitType e elty in
  case op of

    -- Nothing to do here because the ArgRecord will already contain Use
    Use _ -> do comm$ "'Use'd arrays are already available in the arguments record:"
                varinit (emitType e ty) (varSyn outV) (strToSyn globalArgs `arrow` (varSyn outV))
                return ()
    
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
    GenManifest {} -> do
      error$"EmitC.hs/execBind: We don't directly support Generate kernels, they should have been desugared:\n"++show(doc op)

    -- This is unpleasantly repetetive.  It doesn't benefit from the lowering to expose freevars and use NewArray.
    GenReduce {reducer,generator,variant,stride} -> do 
      let (Lam [(v,_,ty1),(w,_,ty2)] bod) = reducer
          Fold initSB = variant
          Manifest inVs = generator
          step = case stride of
                   StrideConst s -> emitE e s
                   StrideAll     -> 1

          -- TEMPORARY:
          [inV] = inVs
      
      initVs <- emitBlock e initSB
      
      -- The builder function also needs any free variables in the size:
      let freevars = arrayOpFVs 
          initargs = map varSyn initVs 
          len = 1  -- Output is fully folded
          insize :: Syntax
          insize  = trivToSyntax$ P.snd$ sizeEnv # inV
          allargs = insize : step : varSyn outV : varSyn inV : initargs ++ map varSyn freevars
          
      varinit (emitType e ty) (varSyn outV) (function "malloc" [sizeof elty' * len])
      -- Call the builder to fill in the array: 
      emitStmt$ (function$ strToSyn$ builderName evtid) allargs
      return ()
            
    _ -> error$"EmitC.hs/execBind: can't handle this array operator yet:\n"++show (doc op)


--------------------------------------------------------------------------------
-- | Generate code to print out a single array of known size.
--   Takes as input the ProgBind that produced the array.
printArray :: (Out a, EmitBackend e) => e -> GPUProg a -> Var -> GPUProgBind a -> EasyEmit ()
printArray e (GPUProg{sizeEnv}) name (GPUProgBind { outarrs, op}) = do
  len <- tmpvar (emitType e TInt)
  let (_,szTriv) = sizeEnv # vr0
  -- TODO: Assert the sizes are all equal.
  case ndims of
     1 -> case szTriv of 
            TrivConst  n -> set len (fromIntegral n)
            TrivVarref v -> set len (varSyn v)
     0  -> set len "1"
     oth -> error$"printArray: not yet able to handle arrays of rank: "++ show oth
  printf " [ " []
  if numbinds == 1
    then printit  0 vr0
    else printtup 0 
  for 1 (E.< len) (+1) $ \ind -> do
     printf ", " []
     if numbinds == 1
       then printit  ind vr0
       else printtup ind
  printf " ] " []
  where
    (vrs,_,tys) = unzip3 outarrs
    (vr0,_,TArray ndims elt) =
      case outarrs of
        h:_ -> h
        []  -> error$"printArray: why are we printing an op with no outputs?:\n"++show(doc op)
    numbinds = length outarrs
    printtup ix = do
      printf "(" []
      printit ix vr0
      forM_ (tail vrs) $ \vr -> do
        printf ", " []        
        printit ix vr
      printf ")" []
    printit :: Syntax -> Var -> EasyEmit ()
    printit ind vr = printf (printfFlag elt) [arrsub (varSyn vr) ind]



--------------------------------------------------------------------------------  
-- Helpers and Junk
--------------------------------------------------------------------------------

include :: String -> EasyEmit ()
include str = emitLine$ toSyntax$ text$ "#include \""++str++"\""

fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a

thd3 :: (t, t1, t2) -> t2
thd3 (_,_,c) = c


trivToSyntax :: TrivialExp -> Syntax
trivToSyntax (TrivConst n)  = fromIntegral n
trivToSyntax (TrivVarref v) = varSyn v

