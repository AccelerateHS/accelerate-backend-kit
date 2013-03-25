{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}
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
import qualified Control.Exception as CE 
import           Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Prelude   as P
import           Prelude (($), (.), show, error, return, mapM_, String, fromIntegral, Int)
import           Text.PrettyPrint.HughesPJ       (text)
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Debug.Trace (trace)

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
    -- include "math.h"    
    case e of
      CEmitter Sequential   _ -> return ()
      CEmitter CilkParallel _ -> do include "cilk/cilk.h"
                                    include "cilk/reducer.h"
    mapM_ (emitLine . strToSyn) $ P.lines headerCode 

  invokeKern (CEmitter CilkParallel _) len body = E.cilkForRange (0,len) body
  invokeKern (CEmitter Sequential _)   len body = E.forRange (0,len) body

  emitType _ = emitCType

  -- In Cilk we use a vectorized ("elemental") function:
  scalarKernelReturnType (CEmitter CilkParallel _) = "__declspec(vector) void"
  scalarKernelReturnType (CEmitter Sequential _)   = "void"

  -- ARGUMENT PROTOCOL: Folds expect: ( inSize, inStride, outArrayPtr ..., inArrayPtr ..., initElems..., kernfreevars...)
  emitGenReduceDef e@(CEmitter typ env) (GPUProgBind{ evtid, outarrs, decor=(FreeVars arrayOpFVs), op }) = do
    let GenReduce {reducer,generator,variant,stride} = op
        -- ONLY work for Fold for now:
        Fold initSB@(ScalarBlock _ initVs _) = variant
        Lam formals bod = reducer

        vs = take (length initVs) formals
        ws = drop (length initVs) formals
        initargs = map (\(vr,_,ty) -> (emitType e ty, show vr)) vs
        outargs  = [ (emitType e outTy, show outV)      | (outV,_,outTy) <- outarrs ]
        inargs   = case generator of
                    Manifest inVs -> [ (emitType e (env # inV), show inV) | inV <- inVs ]
                    NonManifest _ -> []
        freeargs = map (\fv -> (emitType e (env # fv), show fv))
                       arrayOpFVs
        int_t    = emitType e TInt
        void_ptr = "void*"
        builder  = builderName evtid
    
    CE.assert (length initVs == length ws) $ return()
--    CE.assert (length outarrs == length inVs) $ return()    

    rawFunDef "void" builder ((int_t, "inSize") : (int_t, "inStride") : 
                                          outargs ++ inargs ++ initargs ++ freeargs) $ 
         do E.comm$"Fold loop, reduction variable(s): "++show vs
            E.comm$"First, some temporaries to back up the inital state"
            E.comm$" (we're going to stomp on the reduction vars / formal params):"
            tmps <- P.sequence [ E.tmpvarinit (emitType e vty) (varSyn v) | (v,_,vty) <- vs ]
            let body round = do 
                 E.comm$"Fresh round, new accumulator with the identity:"
                 E.comm$"We shadow the formal params as a hack:"
                 P.sequence [ varinit (emitType e vty) (varSyn v) tmp | (v,_,vty) <- vs | tmp <- tmps ]
                 E.forStridedRange (round, 1, round+"inStride") $ \ ix -> do

                   let foldit inputs k =
                         P.sequence$ [ varinit (emitType e wty) (varSyn wvr) (k inV)
                                     | inV <- inputs
                                     | (wvr, _, wty) <- ws ]
                   case generator of
                     Manifest inVs -> foldit inVs (\ v -> arrsub (varSyn v) ix)
                     NonManifest (Gen _ (Lam args bod)) -> do
                       comm "(1) create input: we run the generator to produce one or more inputs"
                       -- TODO: Assign formals to ix
                       let [(vr,_,ty)] = args -- ONE argument, OneDimensionalize
                       E.varinit (emitType e ty) (varSyn vr) ix
                       tmps <- emitBlock e bod
                       comm$"(2) do the reduction with the resulting values ("++show tmps++")"
                       foldit tmps varSyn

                   ----------------------- 
                   tmps <- emitBlock e bod -- Here's the body, already wired to use vs/ws
                   -----------------------
                   -- when dbg $ 
                   --   eprintf " ** Folding in position %d, offset %d (it was %f) intermediate result %f\n"
                   --           [ix, round, (arrsub (varSyn (head inVs)) ix), varSyn$ head tmps]
                   forM_ (fragileZip tmps vs) $ \ (tmp,(v,_,_)) ->
                      set (varSyn v) (varSyn tmp)
                   return ()
                 comm "Write the single reduction result to each output array:"
                 P.sequence $ [ arrset (varSyn outV) (round / "inStride") (varSyn v)
                              | (outV,_,_) <- outarrs
                              | (v,_,_)    <- vs ]
                 return () -- End outer loop
            case typ of
              Sequential   -> E.forStridedRange     (0, "inStride", "inSize") body
              CilkParallel -> E.cilkForStridedRange (0, "inStride", "inSize") body


            return () -- End rawFunDef
    return () -- End emitFoldDef


  emitMain e prog@GPUProg{progBinds, progResults, sizeEnv} = do

    let useBinds   = getUseBinds prog
        allResults = standardResultOrder (map P.fst progResults)
        allUses    = S.fromList $ map (\(a,b,c) -> a) useBinds
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
        let elt = P.fst$ sizeEnv # name 
        if S.member name allUses
        then comm$"NOT freeing "++show name++" because it came in from Haskell."
        else freeCStorage elt (arg `arrow` varSyn name)
      E.emitStmt$ function "free" [arg]
    forM_ allResults $ \ name -> do 
      let elt = P.fst $ sizeEnv#name
      funDef (emitType e (TArray 1 elt)) ("GetResult_" ++ show name) ["struct ResultRecord*"] $ \ results -> do
        return_ (results `arrow` (varSyn name))
      funDef "int" ("GetResultSize_" ++ show name) ["struct ResultRecord*"] $ \ results -> do
        return_ (results `arrow` (varSyn name +++ "_size"))
        
    ----------------------------------------
    mainBody P.False e prog 

    when (null useBinds) $ do 
      comm "As a bonus, we produce a normal main function when there are no Use AST nodes."
      mainBody P.True e prog 

mainBody :: P.Bool -> CEmitter -> GPUProg FreeVars -> EasyEmit ()
mainBody isCMain e prog@GPUProg{progBinds, progResults, sizeEnv} = do 
    let useBinds   = getUseBinds prog
        allResults = standardResultOrder (map P.fst progResults)
        allUses    = S.fromList $ map (\(a,b,c) -> a) useBinds
        body       = do            
           comm "First we EXECUTE the program by executing each array op in order:"
           mapM_ (execBind e prog) (L.zip [0..] progBinds)

           if isCMain then do 
              comm "This code prints the final result(s):"
              forM_ allResults $ \ result -> do 
                printArray e prog result (lkup result progBinds)
                emitStmt$ function "printf" [stringconst "\n"]
            else do 
              comm "We write the final output to the results record:"
              forM_ allResults $ \ rname -> do 
                E.set (strToSyn globalResults `arrow` varSyn rname) (varSyn rname)
                E.set (strToSyn globalResults `arrow` (varSyn rname+++"_size")) $
                  case sizeEnv # rname of 
                    (_, TrivVarref vr) -> (varSyn vr)
                    (_, TrivConst  n)  -> fromIntegral n

           comm "Finally, we free all arrays that are NOT either input or outputs:"
           forM_ progBinds $ \ GPUProgBind { outarrs } -> do
             forM_ outarrs  $ \ (vr,_,ty) ->
               if S.member vr allUses P.|| elem vr allResults
               then return ()
               else freeCStorage ty (varSyn vr)
    _ <- if isCMain
         then rawFunDef "int" "main" [] (do body; return_ 0)
         else rawFunDef "void" "MainProg" [("struct ArgRecord*",globalArgs), ("struct ResultRecord*",globalResults)] body
    return ()

   
-- | This abstracts out the calls to reclaim storage.  If the policy changes on what
-- is heap allocated (currently only TArray), then this needs to change.
freeCStorage :: Type -> Syntax -> EasyEmit ()
freeCStorage ty exp = 
  case ty of
    TArray _ _ -> E.emitStmt$ function "free" [exp]
    _          -> return () -- This is stack allocated.


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
  case op of

    -- Nothing to do here because the ArgRecord will already contain Use
    Use _ -> do comm$ "'Use'd arrays are already available in the arguments record:"
                let [(outV,_,ty)] = outarrs -- Only one output Use's at this point.
                varinit (emitType e ty) (varSyn outV) (strToSyn globalArgs `arrow` (varSyn outV))
                return ()
    
    -- In the case of array conditionals we need to run the scalar
    -- code, then assign the result accordingly.  TODO: this is a
    -- broken kind of eager evaluation currently.  It executes EVERYTHING:
    Cond etest bvr cvr -> do 
      comm "Declare an array (pointer) that will be set based on a conditional:"
      case outarrs of
        [(outV,_,ty)] -> do
          E.var (emitType e ty) (varSyn outV)
          if_ (emitE e etest)
            (set (varSyn outV) (varSyn bvr))
            (set (varSyn outV) (varSyn cvr))
        _ -> error$"EmitC.hs: Cond should have been unzipped, should not have multiple outputs: "++show outarrs

    NewArray numelems -> do
      let len   = emitE e numelems
          [(outV,_,ty)] = outarrs -- Only one output NewArray's at this point.
          TArray _ elty = ty
      varinit (emitType e ty) (varSyn outV) (function "malloc" [sizeof (emitType e elty) * len])
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

    -- This is unpleasantly repetitive.  It doesn't benefit from the lowering to expose freevars and use NewArray.
    GenReduce {reducer,generator,variant,stride} -> do 
      let (Lam [(v,_,ty1),(w,_,ty2)] bod) = reducer
          Fold initSB = variant
      
      initVs <- emitBlock e initSB
      
      let freevars = arrayOpFVs 
          initargs = map varSyn initVs
          outVs   = [ outV | (outV,_,_) <- outarrs ]
          
          insize :: Syntax -- All inputs are the SAME SIZE:
          insize  = case generator of
                      Manifest inVs -> trivToSyntax$ P.snd$ sizeEnv # head inVs
                      NonManifest (Gen tr _) -> trivToSyntax tr
          -- If we are running the Generate ourselves, then we don't have any extra
          -- arguments to pass for the inputs:
          inVs = case generator of
                   Manifest vs   -> vs
                   NonManifest _ -> []
          step = case stride of
                   StrideConst s -> emitE e s
                   StrideAll     -> insize
      
          -- ARGUMENT PROTOCOL, for reduction builder:
          --   (1)  Size in #elements of the complete input array(s)
          --   (2)  Step: how many elements are in each individual reduction.
          --        Size/Step should be equal to the output array(s) size
          --   (3*) Pointers to all output arrays.
          --   (4*) Pointers to any/all input arrays.
          --   (5*) All components of the initial reduction value
          --   (6*) All free variables in the array kernel (arrayOpFVs)
          allargs = insize : step : map varSyn outVs ++ map varSyn inVs ++ initargs ++ map varSyn freevars

      comm "Allocate all ouput space for the reduction operation:"
      P.sequence$ [ varinit (emitType e (TArray nd elty)) (varSyn outV)
                            (function "malloc" [sizeof (emitType e elty) * (insize / step)])
                  | (outV,_,TArray nd elty) <- outarrs ]
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
-- C code to include with all generated files:

-- If this gets any longer, we'd better put it in a separate file read at compile or
-- runtime (or quasiquote).  Unfortunately, all of those options add extra headaches.
headerCode :: String
headerCode =
  P.unlines
  [ "#define max(a,b) ({ __typeof__ (a) _a = (a); __typeof__ (b) _b = (b); _a > _b ? _a : _b; })"
  , "#define min(a,b) ({ __typeof__ (a) _a = (a); __typeof__ (b) _b = (b); _a < _b ? _a : _b; })"
    --  "int min(int a, int b) { return (((a)<(b))?(a):(b)) } "
  ]

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

