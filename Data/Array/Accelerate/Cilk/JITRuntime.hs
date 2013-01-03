
{-# LANGUAGE ScopedTypeVariables #-}

-- | A JIT to compile and run programs via Cilk.  This constitutes a full Accelerate
-- backend.
--
--  TODO: this needs to be fixed to use dlopen for Use to work.  (Reading the results
--  back is currently done by printing them as text -- a hack.)

module Data.Array.Accelerate.Cilk.JITRuntime (run, rawRunIO) where 

import           Data.Array.Accelerate (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc   as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..))
import           Data.Array.Accelerate.BackendKit.CompilerUtils (maybtrace, dbg)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase1, phase2, repackAcc)
import           Data.Array.Accelerate.Shared.EmitC (emitC, ParMode(..))
import           Data.Array.Accelerate.BackendKit.SimpleArray (payloadsFromList)


-- import qualified Data.Map                          as M
import           Data.Char        (isAlphaNum)
import           Control.Monad    (when)
import           System.IO.Unsafe (unsafePerformIO)
import           System.Process   (readProcess, system)
import           System.Exit      (ExitCode(..))
import           System.Directory (removeFile, doesFileExist)
import           System.IO        (stdout, hFlush)

--------------------------------------------------------------------------------

-- Phase 3 passes:
import Data.Array.Accelerate.BackendKit.Phase3.KernFreeVars      (kernFreeVars)
import Data.Array.Accelerate.BackendKit.Phase3.ToGPUIR           (convertToGPUIR)
import Data.Array.Accelerate.BackendKit.Phase3.DesugarGenerate   (desugarGenerate)
import Data.Array.Accelerate.BackendKit.CompilerUtils            (runPass)
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike     as C
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
import           Data.Array.Accelerate.BackendKit.IRs.Metadata   (ArraySizeEstimate, FreeVars)

-- | Run a cut-down version of phase3 of the compiler:
-- 
-- TODO: Express this by enriching the compiler pipeline mechanism and
-- *subtracting* a pass from the existing phase3...
phase3_ltd :: C.LLProg ArraySizeEstimate -> G.GPUProg (ArraySizeEstimate, FreeVars)
phase3_ltd prog = 
  runPass    "desugarGenerate"   desugarGenerate   $     -- (size,freevars)
--  runPass    "desugarFoldScan"   desugarFoldScan   $     -- (size,freevars)
  runPass    "convertToGPUIR"    convertToGPUIR    $     -- (size,freevars)
  runPass    "kernFreeVars"      kernFreeVars      $     -- (size,freevars)
  prog
  
--------------------------------------------------------------------------------


-- | Run an Accelerate computation using a C backend in the given
--   parallelism mode.
run :: forall a . Sug.Arrays a => ParMode -> Acc a -> a
run pm acc =
  maybtrace ("[CilkJIT] Repacking AccArray(s): "++show arrays) $ 
  repackAcc acc arrays
 where
   -- TODO we need a way to reimpose multidimensionality here for this
   -- full "run" interface to work properly.  The LLIR should probably
   -- track the final shape.
   simple = phase1 acc
   arrays = unsafePerformIO $
            rawRunIO pm "" simple

rawRunIO :: ParMode -> String -> S.Prog () -> IO [S.AccArray]
rawRunIO pm name prog = do
  let prog2    = phase3_ltd $ phase2 prog
      emitted  = emitC pm prog2
      thisprog = ".plainC_"++ stripFileName name
  b     <- doesFileExist (thisprog++".c")
  when b $ removeFile    (thisprog++".c") -- Remove file for safety
  writeFile  (thisprog++".c") emitted
  dbgPrint$ "[JIT] Invoking C compiler on: "++ thisprog++".c"

  cc <- case pm of
         Sequential -> return "gcc"
         CilkParallel -> do
           whichICC <- readProcess "which" ["icc"] []
           case whichICC of
             ""  -> error "ICC not found!"
             _   -> dbgPrint $"[JIT] Using ICC at: "++ (head (lines whichICC))
           return "icc"
  
  cd <- system$ cc++" -std=c99 "++thisprog++".c -o "++thisprog++".exe"
  case cd of
    ExitSuccess -> return ()
    ExitFailure c -> error$"C Compiler failed with code "++show c
  -- Run the program and capture its output:
  dbgPrint$ "[JIT] Invoking external executable: "++ thisprog++".exe"
--  ExitSuccess <- system$"./"++thisprog++".exe"
  result <- readProcess ("./"++thisprog++".exe") [] ""
  let elts = tyToElts (S.progType prog)
  dbgPrint$ "[JIT] Executable completed, parsing results, element types "++
     show elts++", "++show (length result)++" characters:\n "++take 80 result
  return$ parseMultiple result elts
 where
   parseMultiple _ [] = []
   parseMultiple str (elt:rst) = 
     let (ls,str2) = readPayload elt str in
     S.AccArray (error "need shape!") (payloadsFromList elt ls) :
     parseMultiple str2 rst
   -- Detuple a tuple of arrays to yield a flat list of element types:
   tyToElts (TArray _ elt) = [elt]
   tyToElts (TTuple ls)    = concatMap tyToElts ls
   tyToElts oth            = error$"expecting array types only as Accelerate return values, not: "++show oth


-- *** TODO ***
-- Implement dynamic library loading and copying array data back from ForeignPtrs .
-- 

-- | Remove exotic characters to yield a filename
stripFileName :: String -> String
stripFileName name = filter isAlphaNum name


-- | Read an AccArray from a string
readPayload :: S.Type -> String -> ([Const],String)
readPayload ty str =
  let go fn = let ((ls,str2):_) = reads str in (map fn ls,str2) in 
  case ty of
    TInt    -> go I
    TInt8   -> go I8
    TInt16  -> go I16
    TInt32  -> go I32
    TInt64  -> go I64
    TWord   -> go W  
    TWord8  -> go W8 
    TWord16 -> go W16
    TWord32 -> go W32
    TWord64 -> go W64
    TFloat  -> go F  
    TDouble -> go D  
    _ -> error$"Cilk/JITRuntime.hs:readPayload: this is a temporary hack!  It doesn't handle "++show ty
--     TCShort -> 
--     TCInt   -> 
--     TCLong  -> 
--     TCLLong -> 
--     TCUShort ->
--     TCUInt   ->
--     TCULong  ->
--     TCULLong ->
--     TCChar -> 1;TCSChar -> 1; TCUChar -> 1; -- C character types.
--     TCFloat -> 4; TCDouble -> 8;
--     TBool -> 1;   TChar -> 1; 
--     TTuple ls -> 
--     TArray _ _ -> 


dbgPrint :: String -> IO ()
dbgPrint str = if not dbg then return () else do
    putStrLn str
    hFlush stdout
