{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE ForeignFunctionInterface  #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A JIT to compile and run programs via Cilk.  This constitutes a full Accelerate
-- backend.
module Data.Array.Accelerate.Cilk.JITRuntime (run, rawRunIO) where 

import           Data.Array.Accelerate (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc   as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..))
import qualified Data.Array.Accelerate.BackendKit.SimpleArray     as SA
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (maybtrace, dbg)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1, phase2, repackAcc)
import           Data.Array.Accelerate.Shared.EmitC (emitC, ParMode(..), getUseBinds, standardResultOrder)
import           Data.Array.Accelerate.BackendKit.SimpleArray (payloadsFromList, payloadFromPtr)
import           Data.Array.Accelerate.Shared.EmitHelpers ((#))

import           Data.Time.Clock  (getCurrentTime,diffUTCTime)
import qualified Data.Map         as M
import           Data.Char        (isAlphaNum)
import           Control.Monad    (when, forM_, forM)
import           Control.Exception (evaluate)
import           System.IO.Unsafe (unsafePerformIO)
import           System.Process   (readProcess, system)
import           System.Exit      (ExitCode(..))
import           System.Directory (removeFile, doesFileExist)
import           System.IO        (stdout, hFlush)
import           System.Environment (getEnvironment)

import           GHC.Prim           (byteArrayContents#)
import           GHC.Ptr            (Ptr(Ptr), castPtr)
import           Data.Array.Base    (UArray(UArray))
import           Foreign.Ptr        (FunPtr)
-- import           Foreign.C.Types    (CInt)
import           System.Posix.DynamicLinker (withDL, RTLDFlags(..), dlsym)
-- import Foreign.Ptr        (Ptr)
--import Data.Array.Unboxed (UArray)

----------------------------------------
-- Phase 3 passes:
import Data.Array.Accelerate.BackendKit.Phase3.KernFreeVars      (kernFreeVars)
import Data.Array.Accelerate.BackendKit.Phase3.ToGPUIR           (convertToGPUIR)
import Data.Array.Accelerate.BackendKit.Phase3.DesugarGenerate   (desugarGenerate)
import Data.Array.Accelerate.BackendKit.Phase3.FuseGenReduce     (fuseGenReduce)
import Data.Array.Accelerate.BackendKit.CompilerPipeline         (runPass)
import qualified Data.Array.Accelerate.BackendKit.IRs.CLike     as C
import qualified Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
import           Data.Array.Accelerate.BackendKit.IRs.Metadata   (ArraySizeEstimate, FreeVars)

----------------------------------------------------------------------------------------------------
-- | Run a cut-down version of phase3 of the compiler:
--   WARNING: CODE DUPLICATION.
-- 
-- TODO: Express this by enriching the compiler pipeline mechanism and
-- *subtracting* a pass from the existing phase3...
phase3_ltd :: C.LLProg () -> G.GPUProg (FreeVars)
phase3_ltd prog = 
  runPass    "desugarGenerate"   desugarGenerate   $     -- (size,freevars)
--  runPass    "desugarFoldScan"   desugarFoldScan   $   -- (size,freevars)
  runPass    "fuseGenReduce"     fuseGenReduce     $     -- (freevars)  
  runPass    "convertToGPUIR"    convertToGPUIR    $     -- (size,freevars)
  runPass    "kernFreeVars"      kernFreeVars      $     -- (freevars)
  prog

cOptLvl = if (dbg>0) then " -O0 " else " -O3 "

--  "-march=pentium-m -msse3 -O{0|1|2|3|s} -pipe".
-- | For ICC we actually strip out the vanilla opt level and use other flags:
stripOptFlag :: String -> String
stripOptFlag = unwords . filter (not . (`elem` ["-O0","-O1","-O2","-O3"])) . words

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
   simple = phase2 $ phase1 $ phase0 acc
   arrays = unsafePerformIO $
            rawRunIO pm "" simple

-- Takes a program for which "phase2" has already been run.
rawRunIO :: ParMode -> String -> C.LLProg () -> IO [S.AccArray]
rawRunIO pm name prog = do
  -----------
  t0 <- getCurrentTime 
  prog2 <- evaluateGPUIR (phase3_ltd prog) -- $ phase2 prog  
  t1 <- getCurrentTime
  dbgPrint 1 $"COMPILETIME_phase3: "++show (diffUTCTime t1 t0)
  -----------

  let emitted  = emitC pm prog2
      thisprog = ".plainC_"++ stripFileName name
  b     <- doesFileExist (thisprog++".c")
  when b $ removeFile    (thisprog++".c") -- Remove file for safety
  writeFile  (thisprog++".c") emitted
  t2 <- getCurrentTime
  dbgPrint 1 $"COMPILETIME_emit: "++show (diffUTCTime t2 t1)
  -----------
  
  dbgPrint 2 $ "[JIT] Invoking C compiler on: "++ thisprog++".c"

  -- TODO, obey the $CC environment variable:
  let pickCC onfail = do
        -- UPDATE: -ww13397 to downgrade to warning, and -wd13397 to disable entirely.  NICE!        
        let icc_args = " -fast -ww13397 -vec-report2 "++ stripOptFlag cOptLvl
        env <- getEnvironment
        case lookup "CC" env of
          Just cc -> do dbgPrint 1$"[JIT] using CC environment variable = "++show cc
                        if cc == "icc" || cc == "icpc"
                         then return$ cc ++ icc_args   
                         else return$ cc ++" "++ cOptLvl
          Nothing -> do 
            code <- system "which icc" 
            case code of
              ExitFailure _  -> onfail
              ExitSuccess    -> do dbgPrint 2 $"[JIT] Found ICC. Using it."
                                   return$ "icc" ++ icc_args
  cc <- case pm of
         Sequential   -> pickCC (return$ "gcc "++cOptLvl)
         CilkParallel -> pickCC (error "ICC not found!  Need it for Cilk backend.")

  let suppress = if dbg>0 then " -g " else " -w " -- No warnings leaking through to the user.
      ccCmd = cc++suppress++" -shared -fPIC -std=c99 "++thisprog++".c -o "++thisprog++".so"
  dbgPrint 2 $ "[JIT]   Compiling with: "++ ccCmd

  t1 <- getCurrentTime 
  cd <- system$ ccCmd
  t2 <- getCurrentTime    
  dbgPrint 1 $"COMPILETIME_C: "++show (diffUTCTime t2 t1)

  case cd of
    ExitSuccess -> return ()
    ExitFailure c -> error$"C Compiler failed with code "++show c
  -- Run the program and capture its output:
#if 0     
  dbgPrint 1$ "[JIT] Invoking external executable: "++ thisprog++".exe"  
  result <- readProcess ("./"++thisprog++".exe") [] ""
  let elts = tyToElts (S.progType prog)
  dbgPrint 1$ "[JIT] Executable completed, parsing results, element types "++
     show elts++", "++show (length result)++" characters:\n "++take 80 result
  return$ parseMultiple result elts
#else
  dbgPrint 2 $ "[JIT]: Working directory: " ++ (unsafePerformIO $ readProcess "pwd" [] [])
  loadAndRunSharedObj prog2 ("./" ++ thisprog++".so")
#endif
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


dbgPrint :: Int -> String -> IO ()
dbgPrint lvl str = if dbg < lvl then return () else do
    putStrLn str
    hFlush stdout


--------------------------------------------------------------------------------

-- | Follow the protocol for creating an argument record (of arrays), running the
-- program, and retrieving the results (see `emitMain`s docs).
loadAndRunSharedObj :: G.GPUProg a -> FilePath -> IO [S.AccArray]
loadAndRunSharedObj prog@G.GPUProg{ G.progResults, G.sizeEnv, G.progType } soName =
  let useBinds   = getUseBinds prog 
      allResults = standardResultOrder progResults
  in
  withDL soName [RTLD_LOCAL,RTLD_LAZY] $ \ dl ->  do
    car  <- dlsym dl "CreateArgRecord"
    dar  <- dlsym dl "DestroyArgRecord"
    main <- dlsym dl "MainProg"
    crr  <- dlsym dl "CreateResultRecord"
    drr  <- dlsym dl "DestroyResultRecord"

    argsRec    <- mkCreateRecord car
    resultsRec <- mkCreateRecord crr    
    forM_ (zip [1..] useBinds) $ \ (ix,(vr,ty,S.AccArray { S.arrDim, S.arrPayloads })) -> do

      dbgPrint 2 $ "[JIT] Attempting to load Use array arg of type "++show ty++" and size "++show arrDim
      
      oneLoad <- dlsym dl ("LoadArg_"++show vr) 
      case arrPayloads of
        [] -> error $ "loadAndRunSharedObj: empty payload list for array " ++ show vr
        _:_:_ -> error$ "loadAndRunSharedObj: cannot handle multi-payload arrays presently: "
                 ++show vr++" with payloads: "++show (length arrPayloads)
        [payload] -> do          
          let ptr = SA.payloadToPtr payload
              [len] = arrDim
          (mkLoadArg oneLoad) argsRec len ptr
          dbgPrint 2$"[JIT] successfully loaded Use arg "++show ix++", type "++show ty          
          return ()

    ----------RUN IT------------
    t1 <- getCurrentTime
    (mkMainProg main) argsRec resultsRec
    t2 <- getCurrentTime    
    ----------------------------

    dbgPrint 1 $ "SELFTIMED: "++show (diffUTCTime t2 t1)
    dbgPrint 2 $ "[JIT] Finished executing dynamically loaded Acc computation!"
    
    arrs <- forM allResults $ \ (rname,snames) -> do
      oneFetch <- dlsym dl ("GetResult_"++show rname)
      oneSize  <- dlsym dl ("GetResultSize_"++show rname)
      ptr  <- mkGetResult oneFetch resultsRec
      size <- mkGetResultSize oneSize resultsRec
      dbgPrint 1$"[JIT] Fetched result ptr: "++show rname++" = "++show ptr++" and size "++show size
      payl <- payloadFromPtr (fst$ sizeEnv # rname) size (castPtr ptr)

      shape <- forM snames $ \ sname -> do
          oneShape  <- dlsym dl ("GetResult_"++show sname)
          mkGetResultSize oneShape resultsRec
      return (S.AccArray shape [payl])
      
    dbgPrint 2 $ "[JIT] Destroying args record: "++show argsRec
    (mkDestroyRecord dar) argsRec
    dbgPrint 2 $ "[JIT] Destroying results record: "++show resultsRec
    (mkDestroyRecord drr) resultsRec
    let table = M.fromList $ zip (map fst allResults) arrs
        results = map (table #) (map fst progResults)
    dbgPrint 3 $ "[JIT] FULL RESULTS read back to Haskell (type "++show progType++"):\n  "++show results
    return results


-- | Shared for CreateArgRecord and CreateResultRecord
type CreateRecordT = IO (Ptr ())
foreign import ccall "dynamic" 
   mkCreateRecord :: FunPtr CreateRecordT -> CreateRecordT

type DestroyRecordT = Ptr () -> IO ()
foreign import ccall "dynamic" 
   mkDestroyRecord :: FunPtr DestroyRecordT -> DestroyRecordT

type LoadArgT = Ptr () -> Int -> Ptr () -> IO ()
foreign import ccall "dynamic" 
   mkLoadArg :: FunPtr LoadArgT -> LoadArgT

-- TODO: Needs to return something.
type MainProgT = Ptr () -> Ptr () -> IO ()
foreign import ccall "dynamic" 
   mkMainProg :: FunPtr MainProgT -> MainProgT

type GetResultT = Ptr () -> IO (Ptr ())
foreign import ccall "dynamic" 
   mkGetResult :: FunPtr GetResultT -> GetResultT

type GetResultSizeT = Ptr () -> IO Int
foreign import ccall "dynamic" 
   mkGetResultSize :: FunPtr GetResultSizeT -> GetResultSizeT



-- Obtains a pointer to the payload of an unboxed array.
--
-- PRECONDITION: The unboxed array must be pinned.
--  (THIS SHOULD ONLY BE USED WITH Accelerate Arrays)
--
{-# INLINE uArrayPtr #-}
uArrayPtr :: UArray Int a -> Ptr a
uArrayPtr (UArray _ _ _ ba) = Ptr (byteArrayContents# ba)

-- TODO: Need to force beyond WHNF probably.
evaluateGPUIR = evaluate

