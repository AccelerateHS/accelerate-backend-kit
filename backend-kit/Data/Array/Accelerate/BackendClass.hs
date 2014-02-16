{-# LANGUAGE CPP          #-}
{-# LANGUAGE Rank2Types   #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Array.Accelerate.BackendClass (
  Backend(..), 
  SimpleBackend(..),
  runWith

  -- Not ready for primetime yet:
  -- PortableBackend(..), CLibraryBackend(..)

) where

-- friends
import           Data.Array.Accelerate
import qualified Data.Array.Accelerate.AST                      as AST
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SACC
import           Data.Array.Accelerate.Trafo.Sharing (convertAcc)

import System.IO.Unsafe (unsafePerformIO)

-- standard libraries
import           Data.ByteString.Lazy                   as B


-- We may want to process already-converted, already-optimized,
-- possibly-tranfsormed programs of the type `AST.Acc`, and our backend
-- should let us.  See `runRaw` below:


-- For this to be useful it also must be possible to use arrays that are
-- already on the remote side in an Accelerate computation.  Thus
-- `useRemote`, akin to `use`.  Compiling it could be tricky; it would
-- need a new AST node, but it's also backend-specific.


-- | Run a complete Accelerate program through the front-end, and the given backend.
--   Optionally takes a name associated with the program.
runWith :: (Backend b, Arrays a) => b -> DebugName -> Acc a -> a
runWith bkend nm prog = unsafePerformIO $ do 
  let cvtd = convertAcc True True True prog
  remote <- runRaw bkend cvtd Nothing 
  copyToHost bkend remote

-- | A low-level interface that abstracts over Accelerate backend code generators and
-- expression evaluation. This takes the internal Accelerate AST representation
-- rather than the surface, HOAS one.  The reason for this is that we may want to
-- process already converted and transformed/optimised programs.
class Show b => Backend b where

  -- | The type of a remote handle on device memory. This is class-associated
  -- because different backends may represent device pointers differently.
  --
  type Remote b r

  -- | A `Blob` as a thing which /may/ help speed up or skip future
  -- computations. For example, this may represent:
  --
  --   - compiled object code for an expression
  --
  --   - an optimised and/or annotated AST containing backend-specific execution
  --     parameters
  --
  type Blob b r

  -------------------------- Compiling and Running -------------------------------

  -- | Compile an already converted/optimized Accelerate program into a binary
  -- blob that can be executed.  Takes a /suggested/ FilePath for where to put
  -- the blob IF it must be written to disk.
  --
  compile :: Arrays a
          => b
          -> FilePath
          -> AST.Acc a
          -> IO (Blob b a)

  -- | Similar to `compile` but for functions Once compiled, the functions can
  -- be invoked repeatedly on the device side without any additional work on the
  -- host.
  --
  compileFun1 :: (Arrays x, Arrays y)
              => b
              -> FilePath
              -> AST.Afun (x -> y)
              -> IO (Blob b (x -> y))

  -- | Run an already-optimized Accelerate program (`AST.Acc`) and leave the
  -- results on the accelerator device.
  --
  -- The result of `runRaw` is both asynchronous uses the constructor `Remote`
  -- to signal that the result is still located on the device rather than the
  -- host.
  --
  -- Optionally, a previously compiled blob may be provided, which /may/ be able
  -- to avoid compilation, but this is backend-dependent.
  --
  runRaw :: (Arrays a)
         => b
         -> AST.Acc a
         -> Maybe (Blob b a)
         -> IO (Remote b a)

  -- | Execute a function of one argument and leave the results on the device.
  --
  runRawFun1 :: (Arrays x, Arrays y)
             => b
             -> AST.Afun (x -> y)
             -> Maybe (Blob b (x -> y))
             -> Remote b x
             -> IO (Remote b y)

  -------------------------- Copying and Waiting  -------------------------------

  -- | Take a copy action immediately if the data is available.  This implies
  -- `wait`; if the data is not available `copyToHost` blocks until it becomes
  -- ready and is copied.
  --
  -- TODO: Consider adding a separate malloc and overwriting copy.
  --
  copyToHost :: Arrays a => b -> Remote b a -> IO a

  -- | If the device uses a separate memory space, allocate memory in the remote
  -- space and transfer the contents of the array to it.
  --
  copyToDevice :: Arrays a => b -> a -> IO (Remote b a)

  -- | Copy a remote array to a backend instance of the same type. Depending on
  -- the backend this might not involve any actual copying (shared memory
  -- multicore) or not involve the host CPU (DMA between CUDA devices).
  --
  copyToPeer :: Arrays a
             => b                       -- ^ destination context
             -> Remote b a              -- ^ the source array data to copy
             -> IO (Remote b a)

  -- | Wait until the result is computed, but do not copy it back.
  --
  waitRemote :: b -> Remote b a -> IO ()

  -- | Inject a remote array into an AST node
  --
  useRemote :: Arrays a => b -> Remote b a -> IO (AST.Acc a)

  -------------------------- Configuration Flags --------------------------------

  -- | Are `copyToDevice` calls complexity O(N) or O(1)?  For example, this
  -- might return True for a discrete GPU and false for an on-chip GPU or CPU
  -- backend.
  --
  separateMemorySpace :: b -> Bool

  -- | When asked to produced Blobs, will this backend always go to disk?
  --
--  compilesToDisk :: b -> Bool

  -- | Convenience function. If a blob is loitering in memory, force it to disk
  --
--  forceToDisk :: Blob b r -> IO (Blob b r)


-- | An optional name for the program being run that may help for debugging purpopes.
type DebugName = Maybe String


-- | An alternative class to Backend which represents a backend that has the ability
-- to handle the simplified AST (SimpleAcc) directly.  
--
-- All methods here are substantially different because in this case we do /not/ have
-- type-level information about the inputs and results of Accelerate computations.
class Show b => SimpleBackend b where

  -- | The type of a remote handle on device memory. This is class-associated
  -- because different backends may represent device pointers differently.
  -- 
  -- For `SimpleBackend`, SimpleRemote represents ONE logical array.  It cannot
  -- represent a tuple of arrays (of tuples).
  type SimpleRemote b

  -- | A `Blob` as a thing which /may/ help speed up or skip future
  -- computations. For example, this may represent:
  --
  --   - compiled object code for an expression
  --
  --   - an optimised and/or annotated AST containing backend-specific execution
  --     parameters
  --
  type SimpleBlob b

  -------------------------- Compiling and Running -------------------------------

  -- | Compile an already converted/optimized Accelerate program into a binary
  -- blob that can be executed.  Takes a /suggested/ FilePath for where to put
  -- the blob IF it must be written to disk.
  --
  simpleCompile :: b
                -> FilePath
                -> SACC.Prog ()
                -> IO (SimpleBlob b)

  -- | Similar to `compile` but for functions Once compiled, the functions can
  -- be invoked repeatedly on the device side without any additional work on the
  -- host.
  --
  simpleCompileFun1 :: b
                    -> FilePath
                    -> SACC.Fun1 (SACC.Prog ())
                    -> IO (SimpleBlob b)

  -- | Run an already-optimized Accelerate program (`AST.Acc`) and leave the results
  -- on the accelerator device.  The list of results should be equal in length to the
  -- `progResults` field of the input `Prog`.
  --
  -- The result of `runRaw` is both asynchronous uses the constructor `Remote`
  -- to signal that the result is still located on the device rather than the
  -- host.
  --
  -- Optionally, a previously compiled blob may be provided, which /may/ be able
  -- to avoid compilation, but this is backend-dependent.
  --
  simpleRunRaw :: b
               -> DebugName
               -> SACC.Prog ()
               -> Maybe (SimpleBlob b)
               -> IO [SimpleRemote b]

  -- | Execute a function that expects N arrays, repeatedly.  Each time the compiled
  --   function is called, it takes inputs that are already on the device, and
  --   returns leaves the results on the device as well.
  --
  -- The list of results should be equal in length to the
  -- `progResults` field of the input `Prog`.
  simpleRunRawFun1 :: b -> Int 
                   -> ([SACC.AVar] -> SACC.Prog ())
                   -> Maybe (SimpleBlob b)
                   -> [SimpleRemote b]
                   -> IO [SimpleRemote b]

  -------------------------- Copying and Waiting  -------------------------------

  -- | Take a copy action immediately if the data is available.  This implies
  -- `wait`; if the data is not available `copyToHost` blocks until it becomes
  -- ready and is copied.
  --
  -- TODO: Consider adding a separate malloc and overwriting copy.
  --
  simpleCopyToHost :: b -> SimpleRemote b -> IO SACC.AccArray

  -- | If the device uses a separate memory space, allocate memory in the remote
  -- space and transfer the contents of the array to it.
  --
  simpleCopyToDevice :: b -> SACC.AccArray -> IO (SimpleRemote b)

  -- | Copy a remote array to a backend instance of the same type. Depending on
  -- the backend this might not involve any actual copying (shared memory
  -- multicore) or not involve the host CPU (DMA between CUDA devices).
  --
  simpleCopyToPeer :: b                       -- ^ destination context
                   -> SimpleRemote b          -- ^ the source array data to copy
                   -> IO (SimpleRemote b)

  -- | Wait until the result is computed, but do not copy it back.
  --
  simpleWaitRemote :: b -> SimpleRemote b -> IO ()

  -- | Inject a remote array into an AST node so that it can be used in a larger
  -- program.
  --
  simpleUseRemote :: b -> SimpleRemote b -> IO SACC.AExp

  -------------------------- Configuration Flags --------------------------------

  -- | Are `copyToDevice` calls complexity O(N) or O(1)?  For example, this
  -- might return True for a discrete GPU and false for an on-chip GPU or CPU
  -- backend.
  --
  simpleSeparateMemorySpace :: b -> Bool

  -- | When asked to produced Blobs, will this backend always go to disk?
  --
--  simpleCompilesToDisk :: b -> Bool

  -- | Convenience function. If a blob is loitering in memory, force it to disk
  --
--  simpleForceToDisk :: SimpleBlob b -> IO (SimpleBlob b)


-- | A type wrapper that "casts" a SimpleBackend into a Backend.
-- 
--   Discarding type information is easy, so we have a subtyping relation in this
--   direction but not the other.
newtype LiftBackend b = LiftBackend b
  deriving Show

instance SimpleBackend b => Backend (LiftBackend b) where
-- FINISHME

{--
-- | A bag of bits that can be serialised to disk
--
data BinaryBlob
  -- | Stored on disk at the given filepath
  = OnDisk FilePath

  -- | Currently in memory and can be serialised to a bytestring on demand. This
  --   filepath is the location that the blob is intended to occupy when flushed
  --   to disk.
  | InMemory FilePath (IO ByteString)

instance Show BinaryBlob where
  show (OnDisk path)    = "OnDisk: " ++ path
  show (InMemory _ _)   = "InMemory <IO>"


-- | If a binary blob is loitering in memory, force it out to the disk
--
flushToDisk :: BinaryBlob -> IO BinaryBlob
flushToDisk blob@(OnDisk _)     = return blob
flushToDisk (InMemory path gen) = do
  B.writeFile path =<< gen
  return $ OnDisk path
--}

----------------------------------------------------------------------------------------------------

-- Brainstorming other interfaces:


-- | A portable backend is one that can compile programs to portable binaries,
-- which can be loaded and run without reference to the original `Acc` code.
--
class Backend b => PortableBackend b where

  -- | Similar to Data.Dynamic.fromDynamic, this only succeeds if the types match.
  --
  runCompiled :: Arrays a => b -> (Blob b a) -> IO (Maybe a)

----------------------------------------------------------------------------------------------------

-- | A library backend can be used to produce standalone C code packaging an
-- Accelerate function for external use. The generated code may have other
-- compile time dependencies, such as CUDA libraries; you must refer to the
-- backend's documentation for details.
--
class Backend b => CLibraryBackend b where
  compileLib :: (Arrays a, Arrays b) => (AST.Acc a -> AST.Acc b) -> ByteString


----------------------------------------------------------------------------------------------------
-- DISCUSSION:
{-

   It would be good if `Remote` could satisfy the `Unlift` type class so that we
   might force part of a tuple of arrays but not all of it.  For example:

       do let (r1,r2) = unlift remote
          copyToHost r1

   Hopefully, it then would be possible to run a large computation DAG, and to get
   back a result computed in the middle, long before the end of the computation
   arrives.

   Even better would be to be able to peek at individual elements without bringing
   the arrays over.  This would be useful for evaluating array-level conditionals CPU
   side.

-}


