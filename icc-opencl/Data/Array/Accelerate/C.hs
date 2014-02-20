{-# LANGUAGE TypeFamilies, CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- CODE used here AND in Cilk.hs... hence all this CPP garbage:

#ifndef MODNAME
#define MODNAME Data.Array.Accelerate.C
#endif
#ifndef BKEND
#define BKEND CBackend
#endif
#ifndef PARMODE
#define PARMODE Sequential
#endif

-- | An entrypoint to an Accelerate backend based on generating C code.
module MODNAME (run, runDetailed, BKEND(..), defaultBackend,
                DbgConf(..), defaultConf) where

import qualified Data.ByteString.Lazy as B
import           System.IO.Unsafe (unsafePerformIO)

import           Data.Array.Accelerate (Acc)
import qualified Data.Array.Accelerate.AST as AST
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.Cilk.JITRuntime as J
import           Data.Array.Accelerate.Shared.EmitC (ParMode(..), DbgConf(..), defaultConf)

import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc   as S
import qualified Data.Array.Accelerate.BackendKit.SimpleArray     as SA
import           Data.Array.Accelerate.BackendClass
import           Data.Array.Accelerate.BackendKit.Utils.Helpers (dbgPrint)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline
                  (phase0, phase1, phase2, repackAcc, unpackArray, Phantom(..))

import Data.Time.Clock  (getCurrentTime,diffUTCTime)
import Control.Exception  (evaluate)
--------------------------------------------------------------------------------

#if 0 
-- Standard boilerplate for lifting a `Backend` instance into a regular `run` function.
run :: forall a . (Sug.Arrays a) => Acc a -> a
run acc = unsafePerformIO $ do
           remt <- (runRaw BKEND (phase0 acc) Nothing)
           copyToHost BKEND remt
#else 
-- Alternatively we can lift up from the `SimpleBackend` interface:
run :: forall a . (Sug.Arrays a) => Acc a -> a
run = runDetailed defaultConf

-- | Run with additional debugging configuration options.
runDetailed :: forall a . (Sug.Arrays a) => DbgConf -> Acc a -> a
runDetailed DbgConf{dbgName, useProcess} acc = unsafePerformIO $ do
           t0 <- getCurrentTime
           p  <- evaluateAccClone$ phase0 acc
           t1 <- getCurrentTime           
           p' <- evaluateSimpleAcc$ phase1 p
           t2 <- getCurrentTime
           dbgPrint 1 $"COMPILETIME_phase0: "++show(diffUTCTime t1 t0)
           dbgPrint 1 $"COMPILETIME_phase1: "++show(diffUTCTime t2 t1)
           remts <- (simpleRunRaw BKEND dbgName p' Nothing)
           arrs  <- mapM (simpleCopyToHost BKEND) remts
           return (repackAcc (undefined :: Acc a) arrs)

#endif


----------------------------------------------------------------------------------------------------
-- The main purpose of this file is to define a new Backend type

-- | This is an abstract type representing the internal state of the backend.
data BKEND = BKEND
  deriving (Show)

-- Nothing to do here but there could be initialization work in the future.
mkCBackend :: IO BKEND
mkCBackend = return BKEND
-- Likewise there could be configuration parameters:
-- data CConfig = CConfig {}
-- defaultCConfig = ...

-- | A default configuration of the backend, expected from every Accelerate
-- implementation, like the "run" method.
defaultBackend :: BKEND
defaultBackend = BKEND

-- | Arrays returned by the generated code.
newtype CRemote a = CRemote [SA.AccArray]
-- FIXME: This should really be left in the ForeignPtr state and should only come
-- back to Haskell when the copyToHost is performed...


-- | For the C backends, a blob is the name of a shared library file.
data CBlob a = CBlob FilePath

-- | Create a new C backend based on the configuration information.

-- | C data is not really very "remote", it just lives on the C heap.
-- newtype CRemote a = ForeignPtr a 
instance Backend BKEND where
  type Remote BKEND a = CRemote a
  type Blob BKEND a = CBlob a 

  compile _ path acc =
    error "C/Cilk backend: separate compile stage not implemented."
--    return (InMemory path (return$ B.empty))

  compileFun1 = error "C/Cilk backend: compileFun1 not implemented yet."

  runRaw _ acc _blob =
    do arrs <- J.rawRunIO PARMODE "" (phase2$ phase1 acc)
       return$ CRemote arrs

--  runFun = error "CBackend: runFun not implemented yet."

  copyToHost = hostCopy
  copyToDevice _b accA = deviceCopy accA
  copyToPeer _ x = return x

  -- No waiting to be done!
  waitRemote _ _ = return ()
  useRemote _ rem = useRem rem
  
  separateMemorySpace _ = False
--  compilesToDisk _ = True

-- For now copying just means repacking
hostCopy :: (Sug.Arrays a) => BKEND -> CRemote a -> IO a
hostCopy _ (CRemote arrays) =
  return$
    repackAcc (undefined :: Acc a) arrays


deviceCopy :: forall a . (Sug.Arrays a) => a -> IO (Remote BKEND a)
deviceCopy acc = do
  let repr :: Sug.ArrRepr a
      repr = Sug.fromArr acc
  -- FIXME: Seems like unpackArray can't really handle an array of tuples.
  let (_,arr,_::Phantom a) = unpackArray repr
      res :: Remote BKEND a
      res = CRemote [arr]
  return res

useRem :: forall a . (Sug.Arrays a) => Remote BKEND a -> IO (AST.Acc a)
useRem rem@(CRemote arrays) =
--  return (AST.Use$ repackAcc (undefined :: Acc a) arrays)
  error "useRemote unfinished for C/Cilk backend instance"


--------------------------------------------------------------------------------

-- | An instance for the less-typed AST backend interface.
instance SimpleBackend BKEND where
  type SimpleRemote BKEND = CRemote SA.AccArray
  type SimpleBlob BKEND = CBlob ()
  
  -- simpleCompile
  -- simpleCompileFun1

  simpleRunRaw _ mname prog _blob =
    do
       let name = case mname of
                   Just n -> n
                   Nothing -> "unknown_prog"
       t1 <- getCurrentTime           
       p  <- evaluateSimpleAcc$ phase2 prog
       t2 <- getCurrentTime
       dbgPrint 1 $"COMPILETIME_phase2: "++show(diffUTCTime t2 t1)
       -- TODO: need to pass these times around if we want to account for all the
       -- stuff inbetween the big pieces.
       arrs <- J.rawRunIO PARMODE name p
       return$ [ CRemote [arr] | arr <- arrs ]

  -- simpleRunRawFun1

  -- These do EFFECTIVELY NOTHING for now:
  simpleCopyToHost _b (CRemote [arr]) = return arr
  simpleCopyToDevice _b arr = return (CRemote [arr])
  simpleCopyToPeer _ x = return x

  simpleUseRemote _ (CRemote [arr]) = return (S.Use arr)
  simpleWaitRemote _ _ = return () -- already copied!
  simpleSeparateMemorySpace _ = False


-- TODO: Need to force beyond WHNF probably.
evaluateAccClone = evaluate
evaluateSimpleAcc = evaluate
