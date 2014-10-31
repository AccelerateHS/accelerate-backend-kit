{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Here we use Haskell type classes in place of inheritance in OOP,
--   to factor out the common code for emiting C or OpenCL.
--
--   This not precisely what type classes are for, so it's a bit of an
--   abuse!

module Data.Array.Accelerate.Shared.EmitCommon
       ( 
         -- * The class definition
         EmitBackend(..), 

         -- * The main entrypoint
         emitGeneric,

         -- * Other bits and pieces
         emitE, emitS, emitBlock, emitConst, emitPrimApp, 
         printfFlag, printf, eprintf, castit, 
         varSyn, strToSyn, lkup
       ) where

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
       ( Type(..), Const(..), Var, var, Prim(..),
         NumPrim(..), IntPrim(..), FloatPrim(..), ScalarPrim(..), BoolPrim(..), OtherPrim(..), 
         constToType, constToInteger, constToRational,
         isFloatConst, isIntConst) 

-- import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.Metadata  (FreeVars(..))
import           Data.Array.Accelerate.Shared.EasyEmit hiding (var)
import qualified Data.Array.Accelerate.Shared.EasyEmit as E
import           Data.Array.Accelerate.Shared.EmitHelpers (builderName, fragileZip)

import           Data.Array.Accelerate.BackendKit.IRs.GPUIR      as G
import           Text.PrettyPrint.HughesPJ      (text, comma)
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

-- | The code emission "superclass", with default definitions for several methods.
--   The methods here factor out functionality that differs between backends.
class EmitBackend e where
  -- | Emit a block of #includes or other header info at the beginning of the file.
  emitIncludes :: e -> EasyEmit ()
  emitIncludes _ = return ()

  -- | Add extra address space qualifiers to function/kernel arguments.
  -- 
  --   Takes a (var,memlocation,type) triple, returns an emitted "type","var" pair.
  decorateArg :: e -> (Var,G.MemLocation,Type) -> (Syntax,String)
  decorateArg e (v,_,ty) = (emitType e ty, show v)

  -- | Given (1D) iteration space size and a function to call the scalar
  -- kernel with an int index, this must invoke the function the right number of times.
  -- This might mean a loop, or for OpenCL/CUDA, the loop is implicit.
  invokeKern :: e -> Syntax -> (Syntax -> EasyEmit ()) -> EasyEmit ()
  
  -- | Convert the type into a printed type in the output language.
  emitType :: e -> Type -> Syntax

  -- | Not relevant in some backends.  Emit a MainProg(void* argR, void* resultR) function that
  -- invokes the kernels.
  -- 
  -- Supporting functions enable argument packaging.  The functions
  -- `CreateArgRecord()`, `LoadArg_<name>(void* argR, int numelems, void* ptr)`, and
  -- `DestroyArgRecord(void* argR)` perform the following functions:
  --   
  --   (1) creating a record to store program inputs (the `Use` arrays),
  --   (2) filling each of its slots with an array
  --   (3) destroying the record after MainProg has been called with it
  --
  --  Likewise, there is a mirroring protocol for result retrieval.
  --  CreateResultRecord, GetResult_<name>(void*), and DestroyResultRecord are the
  --  functions.  There is also a function GetResultSize_<name>(void*), for returning
  --  the number of elements in the result array.
  --
  --  TODO: Standardize when the results are freed so that we can read them back one
  --  at a time.  Presently all are freed simultaneously by DestroyResultRecord.
  -- 
  --  TODO: For some backends we'll want to preallocate the final results on the
  --  Haskell side.
  emitMain :: e -> GPUProg FreeVars -> EasyEmit ()
  emitMain _ _ = return ()

  -- | GenReduce (e.g. Scan/Fold) is not handled by the generic codegen, but this can be overloaded.
  emitGenReduceDef :: (EmitBackend e) => e -> GPUProgBind FreeVars -> EasyEmit ()
  emitGenReduceDef _e op = error$"EmitCommon.hs: GenReduce not supported in this backend:\n "++ show (doc op)

  -- | The (constant) return type for a complete array-level kernel definition. 
  kernelReturnType :: e -> Syntax
  kernelReturnType _ = "void"

  -- | The (constant) return type for a scalar-level kernel definition. 
  scalarKernelReturnType :: e -> Syntax
  scalarKernelReturnType _ = "void"
  


----------------------------------------------------------------------------------------------------
-- Generic code emisson functions:
----------------------------------------------------------------------------------------------------

-- For now we thread an 'e' argument through all functions.  This
-- could also have been done with a Reader monad.

-- | The main entrypoint / compiler pass.
emitGeneric :: (EmitBackend e) => e -> GPUProg (FreeVars) -> String
emitGeneric e prog = show$ execEasyEmit $ do
  emitIncludes e  
  emitKerns e prog  
  emitMain  e prog
  emitLine ""

-- | Emit a series of kernels that implement the program
emitKerns :: ( EmitBackend e) => e -> GPUProg (FreeVars) -> EasyEmit ()
emitKerns e prog@(GPUProg {progBinds}) = do 
  mapM_ (emitBindDef e) (L.zip [0..] progBinds)
  emitLine ""  -- Add a newline.

-- | Creates procedure definitions for a ProgBind.  This typically
--   includes scalar-level function and an array-level function that
--   calls it multiple times to yield an array result.
-- 
--   Expect a definition by the name (builderName evtid).
emitBindDef :: (EmitBackend e) => e -> (Int, GPUProgBind (FreeVars)) -> EasyEmit ()
emitBindDef e (_ind, pb@GPUProgBind{ evtid, op, outarrs } ) =
  case op of
     -- Do NOTHING for scalar binds presently, they will be interpreted CPU-side by JIT.hs:
     ScalarCode _ -> return ()

     -- Cond does not create a *kernel* just more work for the driver/launcher:
     Cond _ _ _ -> return ()
     Use      _ -> return () -- This is also the job of the driver.
     NewArray _ -> return () -- ditto

     ---------------------------------------------------------------------- 
     -- TODO: Handle kernels from 0-3 dimensions:
     Kernel kerniters (Lam formals bodE) _kernargs -> do
       let sizearg  = var "sizeArg"
           sizebind = (sizearg, G.Default, TInt)
           -- TEMP: 1D for now:
           [(ix,_szE)] = kerniters -- Handle 1D only.
           idxargs = [(ix, G.Default, TInt)]

       -- ARGUMENT PROTOCOL: Extra arguments are expected:
       --   * The scalar kernel expects (indices ..., formals ...)  (one index for 1D)
       --   * The array builder expects (size, formals ...)
       -- Thus the caller of the builder function is expected to evaluate the size.
           
       -- (1) Emit a scalar-level procedure:
       -- Use a rawFunDef because we don't want EasyEmit to come up with the variable names:
       kern <- rawFunDefProto (scalarKernelReturnType e)
                              ("kernelFun_"++show evtid)
                              (map (decorateArg e) (idxargs ++ formals)) $ do
         [] <- emitBlock e bodE
         return ()
         
       -- (2) Emit an array-level harness, following the protocol for its argument
       --     list: This function needs both the size argument and the free variables
       --     to pass on to the scalar kernel.
       _ <- rawFunDef (kernelReturnType e)
                      (builderName evtid)
                      (map (decorateArg e) (sizebind : formals)) $       
            -- Call the kernel once and write one element of the output array:            
            do let body i = emitStmt (kern ([i] ++ L.map (varSyn . fst3) formals))
               invokeKern e (varSyn sizearg) body
       return ()
     ----------------------------------------------------------------------
     GenManifest {} -> error$"EmitCommon.hs/emitBindDef: Generate is not supported in generic backend:\n "++ show (doc op)
     GenReduce {} -> emitGenReduceDef e pb

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
    -- SWhile Var (Fun ScalarBlock)  (Fun ScalarBlock) Exp  
    -- Need to replace init with a list of Exp
    -- this list will match up with the args to Lam.
    -- Right now a hack, assume no tuples. 
    SWhile vr (Lam vbinds sb@(ScalarBlock _ _ stms)) 
              (Lam pbinds bod@(ScalarBlock _ out _)) init -> 
        do initOut <- emitBlock e init
           mapM_ (\ ((v, _, t), o) -> E.varinit (emitType e t) (varSyn v) (varSyn o)) $ fragileZip vbinds initOut
           mapM_ (\ ((p, _, t), o) -> E.varinit (emitType e t) (varSyn p) (varSyn o)) $ fragileZip pbinds initOut

           -- evaluate condition before loop
           tmpLst <- emitBlock e sb

           mapM_ (\ ((v, _, _), o) -> emitStmt $
                                      toSyntax $ fromSyntax (varSyn o) <+> "=" <+>
                                      fromSyntax (varSyn v)) $ fragileZip vbinds out
           
           -- ready to write our while loop 
           emitLine $ toSyntax $ "while " <> PP.parens (fromSyntax (varSyn vr))
           block $ do 
              _ <- emitBlock e bod
              -- This assignment has to happen before the condition test!
              mapM_ (\ ((v, _, _), o) -> emitStmt $
                                         toSyntax $ fromSyntax (varSyn v) <+> "=" <+>
                                         fromSyntax (varSyn o)) $ fragileZip vbinds out
              -- emitStmt $ toSyntax $ fromSyntax (varSyn v) <+> "=" <+> fromSyntax (varSyn out)
              mapM_ (emitS e) $ getStms sb
              mapM_ (\ ((p, _, _), o) -> emitStmt $
                                         toSyntax $ fromSyntax (varSyn p) <+> "=" <+>
                                         fromSyntax (varSyn o)) $ fragileZip pbinds out
              --emitStmt $ toSyntax $ fromSyntax (varSyn p) <+> "=" <+> fromSyntax (varSyn out)
              -- assign params  tmp (not needed?)
              return () 

              -- mapM_ (emitS e) stms
           -- block $ emitBlock  
        
    -- let init = emitE e init
        

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

getStms (ScalarBlock _ _ stms) = stms    

-- FIXME: maps an expression onto Syntax... this doesn't allow multi-line.
emitE :: EmitBackend e => e -> Exp -> Syntax
emitE e = loop M.empty 
 where 
   loop mp exr = 
    case exr of    
      EVr  v                -> M.findWithDefault (varSyn v) v mp
      -- We could make this smarter about C literal syntax:
      EConst c              -> castit e (constToType c) (emitConst e c)
      ECond e1 e2 e3        -> loop mp e1 ? loop mp e2 .: loop mp e3
      EPrimApp ty p es      -> -- castit e ty $
                               emitPrimApp e ty p (L.map (loop mp) es)
      EIndexScalar vr ex    -> varSyn vr ! loop mp ex

      EGetLocalID  i -> function "get_local_id"  [fromIntegral i]
      EGetGlobalID i -> function "get_global_id" [fromIntegral i]
            
--      EUnInitArray _ _ -> error$"EmitCommon.hs/emitE: EUnInitArray should only be called as a kernel argument."
      EUnInitArray _ _ -> "ERROR_DONT_USE_EUnInitArray_HERE"

-- | Add a cast around an expression.
castit :: EmitBackend e => e -> Type -> Syntax -> Syntax
castit e ty exp = (E.parens (emitType e ty)) +++ E.parens exp

-- | The new contract [2013.03.07] is that primitive applications depend on their
-- inputs being uniquely typed (and the outputs are not cast).
emitConst :: EmitBackend e => e -> Const -> Syntax
emitConst e cnst = 
  case cnst of
    I _ ->cast;    I8 _ ->cast;    I16 _  ->cast;  I32 _  ->i;  I64 _ ->castl;
    W _ ->castu;    W8 _ ->castu;    W16 _  ->castu;  W32 _  ->castu;  W64 _ ->castul;
    CS _ ->i;  CI _ ->i;  CL _ ->l;  CLL _ ->ll; 
    CUS _ ->u;  CUI _ ->u;  CUL _ ->ul;  CULL _ ->ull;
    CC _ -> i; CSC _ -> i; CUC _ -> u; -- C char types count as ints.
    F  f -> strToSyn$ show f++"f"
    CF f -> strToSyn$ show f++"f"    
    D  f -> strToSyn$ show f
    CD f -> strToSyn$ show f
    C chr   -> strToSyn$ show chr
    B True  -> strToSyn$ "1"
    B False -> strToSyn$ "0"
    Tup []  -> strToSyn$ "0" -- Unit type. 
    Tup _  -> error$"emitConst: no support for tuple constants presently: "++show cnst
 where
   iS    = show (constToInteger cnst)
   i     = strToSyn  iS
   l     = strToSyn$ iS ++ "l"
   ll    = strToSyn$ iS ++ "ll"
   u     = strToSyn$ iS ++ "u"
   ul    = strToSyn$ iS ++ "ul"
   ull   = strToSyn$ iS ++ "ull"   
   cast   = castit e (constToType cnst) i
   castl  = castit e (constToType cnst) l
   castu  = castit e (constToType cnst) u
   castul = castit e (constToType cnst) ul



-- | Emit a PrimApp provided that the operands have already been convinced to `Syntax`.
--   It returns EasyEmit `Syntax` representing a C expression.
emitPrimApp :: EmitBackend e => e -> Type -> Prim -> [Syntax] -> Syntax
emitPrimApp e outTy prim args = 
--  trace ("emitPrimApp: "++ show(outTy, prim, args))$ 
  E.parens$ 
  case prim of
    NP np -> case np of
              Add -> binop "+"
              Sub -> binop "-"
              Mul -> binop "*"
              Neg -> unary "-"
              Abs -> unary "abs"
              -- Warning, potential for code duplication here.  Should ensure that args are trivial:
              Sig ->  (arg E.> 0) E..| (- (arg E.< 0))
    IP ip -> case ip of
              -- This uses the stdlib.h div function, not available in OpenCL:
              -- Quot -> (binfun "div") `dot` (constant "quot")
              -- Rem  -> (binfun "div") `dot` (constant "rem")
              Quot -> binop "/"
              Rem  -> binop "%"
              -- These two need to round towards negative infinity:
              IDiv -> error "integer division truncated towards negative infinity... not implemented yet!"
              Mod  -> error "integer modulus truncated towards negative infinity... not implemented yet!"
              BAnd -> binop "&"
              BOr  -> binop "|"
              BXor -> binop "^"
              BNot -> unary  "~"
              BShiftL -> binop "<<"
              BShiftR -> binop ">>"
              BRotateL -> (left E.<< right) .| (left E.>> ((sizeof right) * 8 - 1))
              BRotateR -> (left E.>> right) .| (left E.<< ((sizeof right) * 8 - 1))
    FP p -> case p of
              Recip -> E.parens (1 / arg) 
              Sin  -> unary "sin"
              Cos  -> unary "cos"
              Tan  -> unary "tan"
              Asin -> unary "asin"
              Acos -> unary "acos"
              Atan -> unary "atan"
              Asinh -> unary "asinh"
              Acosh -> unary "acosh"
              Atanh -> unary "atanh"
              ExpFloating -> unary "expf"
              Sqrt  -> case outTy of
                         TFloat  -> unary "sqrtf"
                         TDouble -> unary "sqrt"
              Log   -> unary "log" -- natural log
              FDiv    -> binop "/"
--              FPow    -> binfun "expt"
              FPow    -> binfun "pow"
              LogBase -> binop "log"
              Atan2   -> unary "atan2"
              Round   -> unary "round"
              Floor   -> unary "floor"
              Ceiling -> unary "ceil"
              -- The C CAST effectively truncate:
              Truncate -> castit e outTy arg
    SP p -> case p of
              Lt   -> binop "<"
              Gt   -> binop ">"
              LtEq -> binop "<="
              GtEq -> binop ">="
              Eq   -> binop "=="
              NEq  -> binop "!="
              Max  -> binfun "max" -- These are not basic standard C
              Min  -> binfun "min" -- they need to be provided.
              -- TODO: Case on Type:
              -- Max  -> case outTy of
              --           TFloat  -> binfun "fmaxf"
              --           TDouble -> binfun "fmax"
              -- Min  -> case outTy of
              --           TFloat  -> binfun "fminf"
              --           TDouble -> binfun "fmin"
    BP p -> case p of
              And  -> binop "&&"
              Or   -> binop "||"
              Not  -> unary "!" 
    OP p -> case p of
              FromIntegral -> castit e outTy arg -- Again, depend on the cast.
              BoolToInt    -> arg
              Ord          -> arg
              S.Chr        -> arg
  where
   t = text
   [left,right] = args
   [arg]        = args -- laziness in action

   argD   = fromSyntax arg
   leftD  = fromSyntax left
   rightD = fromSyntax right
   
   -- No parens for a binop, that is handled by the caller of `emitPrimApp`:
   binop op  = left +++ toSyntax (text (" "++op++" ")) +++ right
   binfun op = toSyntax (text op <> PP.parens (leftD <> comma <> rightD))
   unary  op = toSyntax$ text op <> PP.parens argD


--------------------------------------------------------------------------------  
-- Helpers and Junk
--------------------------------------------------------------------------------

varSyn :: Var -> Syntax
varSyn = toSyntax . text . show

printfFlag :: Type -> String
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
    TTuple [] -> "%d"
    TTuple _ -> error$ "EmitCommon.hs/printfFlag cannot handle tuple types: "++show ty
    TArray _ _ -> error$ "EmitCommon.hs/printfFlag cannot handle array types: "++show ty

-- Silly boilerplate -- look up in a list.
lkup :: Var -> [GPUProgBind t] -> GPUProgBind t
lkup vr pbs = 
  case L.find (\ (GPUProgBind {outarrs}) -> L.elem vr (map fst3 outarrs)) pbs of
    Just x -> x
    Nothing -> error$"EmitCommon.hs/lkup: lookup of var in progbinds failed: "++show vr

-- | Printf to stdout.
printf :: String -> [Syntax] -> EasyEmit ()
printf str ls = emitStmt$ function "printf" (stringconst str : ls)

-- | Printf to stderr.
eprintf :: String -> [Syntax] -> EasyEmit ()
eprintf str ls = emitStmt$ function "fprintf" ("stderr" : stringconst str : ls)


strToSyn :: String -> Syntax
strToSyn = toSyntax . text

fst3 :: (t, t1, t2) -> t
fst3 (v,_,_) = v


-- test0 = emitPrimApp undefined TInt (NP Sig) [constant "x"]
-- test1 = emitPrimApp undefined TInt (IP Quot) [constant "x", constant "y"]

