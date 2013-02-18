
-- DUPLICATED CODE (from Cilk.hs) -- TODO: GENERATE AUTOMATICALLY.

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The entrypoint to an Accelerate backend based on generating sequential C code.
module Data.Array.Accelerate.C (run, CBackend, mkCBackend) where

import qualified Data.ByteString.Lazy as B
import           System.IO.Unsafe (unsafePerformIO)

import           Data.Array.Accelerate (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.Cilk.JITRuntime as J
import           Data.Array.Accelerate.Shared.EmitC (ParMode(..))

import qualified Data.Array.Accelerate.BackendKit.SimpleArray     as SA
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1, phase2, repackAcc)
import           Data.Array.Accelerate.BackendClass 

--------------------------------------------------------------------------------


-- Standard boilerplate for lifting a `Backend` instance into a regular `run` function.
run :: Sug.Arrays a => Acc a -> a
run acc = unsafePerformIO $ do
           rem <- runRaw CBackend (phase0 acc) Nothing
           copyToHost CBackend rem
          
----------------------------------------------------------------------------------------------------
-- The main purpose of this file is to define a new Backend type

-- | This is an abstract type representing the internal state of the backend.
data CBackend = CBackend
  deriving (Show)

-- Nothing to do here but there could be initialization work in the future.
mkCBackend :: IO CBackend
mkCBackend = return CBackend
-- Likewise there could be configuration parameters:
-- data CConfig = CConfig {}
-- defaultCConfig = ...


-- | Create a new C backend based on the configuration information.

-- | C data is not really very "remote", it just lives on the C heap.
-- newtype CRemote a = ForeignPtr a 

-- FIXME: This should really be left in the ForeignPtr state and should only come
-- back to Haskell when the copyToHost is performed...
newtype CRemote a = CRemote [SA.AccArray]

instance Backend CBackend where
  type Remote CBackend a = CRemote a

  compile _ path acc = error "CBackend: separate compile stage not implemented."
--    return (InMemory path (return$ B.empty))

  compileFun = error "CBackend: compileFun not implemented yet."

  runRaw _ acc _blob =
    do arrs <- J.rawRunIO Sequential "" (phase1 acc)
       return$ CRemote arrs

  runFun = error "CBackend: runFun not implemented yet."

  copyToHost = hostCopy

  -- No waiting to be done!
  wait _ _rem = return ()
  
  copyToDevice _ a = error "CBackend: copyToDevice can't work until the Accelerate AST is overhauled."
    
  useRemote = error "CBackend: useRemote can't work until the Accelerate AST is overhauled."
  
  separateMemorySpace _ = False
  compilesToDisk _ = True

-- For now copying just means repacking
hostCopy :: forall a . Sug.Arrays a => CBackend -> CRemote a -> IO a
hostCopy _ (CRemote arrays) =
  return$
    repackAcc (undefined :: Acc a) arrays
