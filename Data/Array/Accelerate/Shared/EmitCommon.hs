{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Here we use Haskell type classes in place of inheritance in OOP,
--   to factor out the common code for emiting C or OpenCL.
--
--   This not precisely what type classes are for, so it's a bit of an
--   abuse!

module Data.Array.Accelerate.Shared.EmitCommon
       ( EmitBackend(..), 
         emitE, emitS, emitBlock, emitGeneric, emitConst,
         printfFlag, printf,
         varSyn, strToSyn, lkup,
         getSizeE, getSizeOfPB
       ) where

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
           ( Type(..), Const(..), Var, var,
             constToType, constToInteger, constToRational,
             isFloatConst, isIntConst)

import           Data.Array.Accelerate.Shared.EasyEmit hiding (var)
import qualified Data.Array.Accelerate.Shared.EasyEmit as E
import           Data.Array.Accelerate.Shared.EmitHelpers (emitPrimApp, builderName)

import           Data.Array.Accelerate.BackendKit.IRs.GPUIR      as G
import           Text.PrettyPrint.HughesPJ      (text)
import           Data.List                      as L
import           Data.Maybe                     (fromJust)
import qualified Data.Map                       as M
import           Control.Monad
import           Prelude                        as P
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Text.PrettyPrint.HughesPJ      as PP ((<>), (<+>), semi, parens) 
import           Debug.Trace                    (trace)

----------------------------------------------------------------------------------------------------
-- First, the interface for the pieces of this code emitter that are FACTORED OUT:

class EmitBackend e where
  -- | Emit a block of #includes or other header info at the beginnign of the file.
  emitIncludes :: e -> EasyEmit ()
  emitIncludes _ = return ()

  -- | Add extra address space qualifiers to function/kernel arguments.
  -- 
  --   Takes a (var,memlocation,type) triple, returns an emitted "type","var" pair.
--  decorateArg :: e -> Type -> G.MemLocation -> (Syntax,String) -> (Syntax,String)  
  decorateArg :: e -> (Var,G.MemLocation,Type) -> (Syntax,String)
  decorateArg e (v,_,ty) = (emitType e ty, show v)

  -- | Given iteration space size and a function to call the scalar
  -- kernel, this must invoke the function the right number of times.
  -- This might mean a loop, or for OpenCL/CUDA, the loop is implicit.
  invokeKern :: e -> Syntax -> (Syntax -> EasyEmit ()) -> EasyEmit ()
  
  -- | Convert the type into a printed type in the output language.
  emitType :: e -> Type -> Syntax

  -- | Emit a main() function that invokes the kernels.  Not relevant in some backends.
  emitMain :: e -> GPUProg () -> EasyEmit ()
  emitMain _ _ = return ()

  kernelReturnType :: e -> Syntax
  kernelReturnType _ = "void"

----------------------------------------------------------------------------------------------------
-- Generic code emisson functions:

-- For now we thread an 'e' argument through all functions.  This
-- could also have been done with a Reader monad.

-- | The main entrypoint / compiler pass.
emitGeneric :: EmitBackend e => e -> GPUProg () -> String
emitGeneric e prog = show$ execEasyEmit $ do
  emitIncludes e  
  emitKerns e prog  
  emitMain  e prog
  emitLine ""

-- | Emit a series of kernels that implement the program in OpenCL.
emitKerns :: EmitBackend e => e -> GPUProg () -> EasyEmit ()
emitKerns e prog@(GPUProg {progBinds}) = do 
  mapM_ (emitBindDef e prog) (L.zip [0..] progBinds)
  emitLine ""  -- Add a newline.


-- | Creates procedure definitions for a ProgBind.  This typically
--   includes scalar-level function and an array-level function that
--   calls it multiple times to yield an array result.
emitBindDef :: EmitBackend e => e -> GPUProg () -> (Int, GPUProgBind ()) -> EasyEmit ()

-- Do NOTHING for scalar binds presently, they will be interpreted CPU-side by JIT.hs:
emitBindDef _ _ (_, GPUProgBind{ op=(ScalarCode _) }) = return ()

emitBindDef e GPUProg{} (_ind, GPUProgBind{ evtid, op} ) =
  let
      -- (TArray dim elty) = aty
      -- aty'   = emitType e aty
      -- elty'  = emitType e elty
      -- [(name,_,aty)] = outarrs -- Laziness: use only in the right places.
      
      -- -- Extra arguments passing a pointer to the OUTPUT array:
      -- outsizearg = decorateArg e TInt (emitType e TInt, "outsize")
      -- outarg     = decorateArg e aty (aty', "out")
      -- arrlen = if dim == 1 then "outsize" else 1     
  in 
  case op of
     -- Cond does not create a *kernel* just more work for the driver/launcher:
     Cond _ _ _ -> return ()

     Use      _ -> return () -- This is also the job of the driver.
     NewArray _ -> return () -- ditto

     ----------------------------------------------------------------------
     -- TODO: Handle kernels from 0-3 dimensions:
     Kernel [(ix,szE)] (Lam formals bodE) kernargs -> do
       let -- Force the size expression to be TRIVIAL for now:
           -- TODO: Make it a simple Either type instead:
           sizefree = -- map undefined (S.toList (expFreeVars szE))
                      case szE of
                        EConst _ -> [(var "ignored", G.Default, TInt)]
                        EVr v    -> [(v, G.Default, TInt)]
           -- TEMP: 1D for now:
           idxargs = [(ix, G.Default, TInt)]
           
       -- (1) Emit a scalar-level procedure:
       -- Use a rawFunDef because we don't want EasyEmit to come up with the variable names:
       kern <- rawFunDefProto "void" ("kernelFun_"++show evtid)
                                     (map (decorateArg e) (idxargs ++ formals)) $ do
         [] <- emitBlock e bodE
         return ()
         
       -- (2) Emit an array-level harness, following the protocol for its argument list:
       --     This function needs both the free variables to pass on to the scalar kernel
       --     AND the free variables used in the size computation.
       _ <- rawFunDef (kernelReturnType e)
                      (builderName evtid)
                      (map (decorateArg e) (sizefree ++ formals)) $       
            -- Call the kernel once and write one element of the output array:            
--            do let body i = emitStmt (kern ([i] ++ L.map (emitE e) kernargs))
            do let body i = emitStmt (kern ([i] ++ L.map (varSyn . fst3) formals))
               invokeKern e (emitE e szE) body
       return ()
     ----------------------------------------------------------------------
     _ -> error$"EmitCommon.hs/emitBindDef: this operator is not supported in the backend:\n "++ show (doc op)
 where
   int_t = emitType e TInt


emitBindDef _ _ (_, GPUProgBind { outarrs=_:_ }) =
  error$"EmitCommon.hs/emitBindDef: cannot handle multi-array-variable bindings yet."

-- | Emit a block of scalar code, returning the variable names which hold the results.
emitBlock :: EmitBackend e => e -> ScalarBlock -> EasyEmit [Var]
emitBlock e (ScalarBlock binds rets stmts) = do
  forM_ binds $ \ (vr,_,ty) ->
    E.var (emitType e ty) (varSyn vr)
  mapM_ (emitS e) stmts
  return rets

emitS :: EmitBackend e => e -> Stmt -> EasyEmit ()
emitS e stmt =
  case stmt of
    SComment str -> E.emitLine (strToSyn ("// "++str))
    SSet vr ex  -> E.set (varSyn vr) (emitE e ex)
    SCond a b c -> if_ (emitE e a)
                       (mapM_ (emitS e) b)
                       (mapM_ (emitS e) c)
    SArrSet a ix rhs -> arrset (varSyn a) (emitE e ix) (emitE e rhs)
    SNoOp            -> return ()
    -- We do a lame bit of remaning here:
    SFor vr init test incr body -> do
       let init' = emitE e init
           test' = emitE e test
           incr' = emitE e incr
           body' = mapM_ (emitS e) body
       let vr' = text(show vr)
           s1 = "int" <+> vr' <+> "=" <+> fromSyntax init'
           s2 = fromSyntax$ test'
           s3 = vr' <+> "=" <+> (fromSyntax$ incr')

       emitLine$ toSyntax ("for " <> PP.parens (s1 <> semi <+>
                                                s2 <> semi <+>
                                                s3)) 
       block body'

--    SSynchronizeThreads -> error$"EmitCommon.hs/emitS: cannot handle SSynchronizeThreads in this generic version"
    SSynchronizeThreads -> emitStmt "barrier(CLK_GLOBAL_MEM_FENCE)"
    

-- FIXME: maps an expression onto Syntax... this doesn't allow multi-line.
emitE :: EmitBackend e => e -> Exp -> Syntax
emitE e expr = loop M.empty expr
 where 
   loop mp exr = 
    case exr of    
      EVr  v                -> M.findWithDefault (varSyn v) v mp
      -- We could make this smarter about C literal syntax:
      EConst c              -> castit (constToType c) (emitConst c)
      ECond e1 e2 e3        -> loop mp e1 ? loop mp e2 .: loop mp e3
      EPrimApp ty p es      -> castit ty
                               (emitPrimApp p (L.map (loop mp) es))
      EIndexScalar vr ex    -> varSyn vr ! loop mp ex

      EGetLocalID  i -> function "get_local_id"  [fromIntegral i]
      EGetGlobalID i -> function "get_global_id" [fromIntegral i]
            
--      EUnInitArray _ _ -> error$"EmitCommon.hs/emitE: EUnInitArray should only be called as a kernel argument."
      EUnInitArray _ _ -> "ERROR_DONT_USE_EUnInitArray_HERE"

   -- | Add a cast around an expression.
   castit :: Type -> Syntax -> Syntax
   castit ty exp = E.parens ((E.parens (emitType e ty)) +++ exp)


emitConst :: Const -> Syntax
emitConst cnst = strToSyn$ 
  case cnst of
    c | isIntConst c   -> show (constToInteger c)
    c | isFloatConst c -> show ((fromRational$ constToRational c)::Double)
    C chr   -> show chr
    B True  -> "1"
    B False -> "0"
    Tup []  -> "0" -- Unit type. 
    Tup _  -> error "emitConst: no support for tuple constants presently."
    _ -> error "internal error: this can never happen"


--------------------------------------------------------------------------------

-- Get an expression representing the size of an output array:
getSizeE :: EmitBackend e => e -> TopLvlForm -> [Exp]
getSizeE _ ae = 
  case ae of 
    Generate exs _ -> exs
    -- Uh oh, we may need to keep around more information earlier...
    _ -> error$"EmitC.hs/getSizeE: cannot handle this yet: "++show ae


getSizeOfPB :: EmitBackend e => e -> GPUProgBind a -> [Exp]
getSizeOfPB e (GPUProgBind{op}) = getSizeE e op

--------------------------------------------------------------------------------  
-- Helpers and Junk
--------------------------------------------------------------------------------

varSyn :: Var -> Syntax
varSyn = toSyntax . text . show

printfFlag ty = 
  case ty of 
    TInt    -> "%d"
    TInt8   -> "%hhd"        
    TInt16  -> "%hd"
    TInt32  -> "%ld"
    TInt64  -> "%lld"
    TWord   -> "%u"
    TWord8  -> "%hhu"
    TWord16 -> "%hu"
    TWord32 -> "%lu"
    TWord64 -> "%llu"
    TFloat  -> "%f"
    TDouble -> "%lf"
    TCFloat  -> "%f"
    TCDouble -> "%lf"    
    TCShort -> "%hd"
    TCInt   -> "%d"
    TCLong  -> "%ld"
    TCLLong -> "%lld"
    TCUShort ->"%hu"
    TCUInt   ->"%u"
    TCULong  ->"%lu"
    TCULLong ->"%llu"
    TChar   -> "%c"
    TCChar  -> "%c"    
    TCUChar -> "%hhu"
    TCSChar -> "%hhd"
    TBool   -> "%hhu"
    TTuple _ -> error$ "EmitCommon.hs/printfFlag cannot handle tuple types: "++show ty
    TArray _ _ -> error$ "EmitCommon.hs/printfFlag cannot handle array types: "++show ty

-- Silly boilerplate -- look up in a list.
lkup :: Var -> [GPUProgBind t] -> GPUProgBind t
lkup vr pbs = 
  case L.find (\ (GPUProgBind {outarrs}) -> L.elem vr (map fst3 outarrs)) pbs of
    Just x -> x
    Nothing -> error$"EmitCommon.hs/lkup: lookup of var in progbinds failed: "++show vr

printf :: ([Syntax] -> Syntax)
printf = function "printf"

strToSyn :: String -> Syntax
strToSyn = toSyntax . text

fst3 :: (t, t1, t2) -> t
fst3 (v,_,_) = v
