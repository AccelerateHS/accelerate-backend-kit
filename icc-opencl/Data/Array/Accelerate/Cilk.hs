{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The entrypoint to an Accelerate backend based on Cilk.
module Data.Array.Accelerate.Cilk (run, CilkBackend, mkCilkBackend) where

import qualified Data.ByteString.Lazy as B
import           System.IO.Unsafe (unsafePerformIO)

import           Data.Array.Accelerate (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.Cilk.JITRuntime as J
import           Data.Array.Accelerate.Shared.EmitC (ParMode(..))

import qualified Data.Array.Accelerate.BackendKit.SimpleArray     as SA
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1, phase2, repackAcc)
import           Data.Array.Accelerate.BackendClass 

-- run = undefined
-- mkCilkBackend = undefined
-- data CilkBackend = CilkBackend
--   deriving (Show)


--------------------------------------------------------------------------------


-- Standard boilerplate for lifting a `Backend` instance into a regular `run` function.
run :: Sug.Arrays a => Acc a -> a
run acc = unsafePerformIO $ do
           rem <- runRaw CilkBackend (phase0 acc) Nothing
           copyToHost CilkBackend rem
          
----------------------------------------------------------------------------------------------------
-- The main purpose of this file is to define a new Backend type

-- | This is an abstract type representing the internal state of the backend.
data CilkBackend = CilkBackend
  deriving (Show)

-- Nothing to do here but there could be initialization work in the future.
mkCilkBackend :: IO CilkBackend
mkCilkBackend = return CilkBackend
-- Likewise there could be configuration parameters:
-- data CilkConfig = CilkConfig {}
-- defaultCilkConfig = ...


-- | Create a new Cilk backend based on the configuration information.

-- | Cilk data is not really very "remote", it just lives on the C heap.
-- newtype CilkRemote a = ForeignPtr a 

-- FIXME: This should really be left in the ForeignPtr state and should only come
-- back to Haskell when the copyToHost is performed...
newtype CilkRemote a = CilkRemote [SA.AccArray]

instance Backend CilkBackend where
  type Remote CilkBackend a = CilkRemote a

  compile _ path acc = error "CilkBackend: separate compile stage not implemented."
--    return (InMemory path (return$ B.empty))

--  compileFun = error "CilkBackend: compileFun not implemented yet."

  runRaw _ acc _blob =
    do arrs <- J.rawRunIO CilkParallel "" (phase2$ phase1 acc)
       return$ CilkRemote arrs

--  runFun = error "CilkBackend: runFun not implemented yet."

  copyToHost = hostCopy

  -- No waiting to be done!
  waitRemote _rem = return ()
  
  copyToDevice _ a = error "CilkBackend: copyToDevice can't work until the Accelerate AST is overhauled."
    
  useRemote = error "CilkBackend: useRemote can't work until the Accelerate AST is overhauled."
  
  separateMemorySpace _ = False
  compilesToDisk _ = True

-- For now copying just means repacking
hostCopy :: forall a . Sug.Arrays a => CilkBackend -> CilkRemote a -> IO a
hostCopy _ (CilkRemote arrays) =
  return$
    repackAcc (undefined :: Acc a) arrays
