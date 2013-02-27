{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}

module Data.Array.Accelerate.BackendClass
       (Backend(..), PortableBackend(..), CLibraryBackend(..),
        Blob(..), forceToDisk)
       where

import           Data.Array.Accelerate
import qualified Data.Array.Accelerate.AST as AST
import           Data.ByteString.Lazy as B

-- We may want to process already-converted, already-optimized,
-- possibly-tranfsormed programs of the type `AST.Acc`, and our backend
-- should let us.  See `runRaw` below:


-- For this to be useful it also must be possible to use arrays that are
-- already on the remote side in an Accelerate computation.  Thus
-- `useRemote`, akin to `use`.  Compiling it could be tricky; it would
-- need a new AST node, but it's also backend-specific.

-- | A `Blob` is a binary object which /may/ help speed up or skip future compilations.
data Blob = OnDisk FilePath -- ^ It's already out on the disk.
            -- | It's in memory and can be serialized to a lazy bytestring on demand:
            --   This keeps around the original filepath that it was *intented* to occupy.
          | InMemory FilePath (IO ByteString)

instance Show Blob where
  show (OnDisk p)   = "OnDisk "++p
  show (InMemory _ _) = "InMemory <IO>"
  
-- | A low-level interface that abstracts over Accelerate backend code generators.
class Show b => Backend b where
  
  -- | The type of a remote handle on device memory.  This is class-associated
  -- because different backends may represent device pointers differently.
  type Remote b r

  -------------------------- Compiling and Running -------------------------------

  -- | Compile an already converted/optimized Accelerate program into a binary blob
  -- that can be executed.  Takes a /suggested/ FilePath for where to put the blob IF
  -- it must be written to disk.
  compile :: Arrays a => b -> FilePath -> AST.Acc a -> IO Blob

  -- | Similar to `compile` but for functions Once compiled, the functions can be
  -- invoked repeatedly on the device side without any additional work on the host.
  compileFun :: (Arrays x, Arrays y) => b -> FilePath -> (AST.Acc x -> AST.Acc y) -> IO Blob

  -- | Run an already-optimized Accelerate program (`AST.Acc`) and leave the results
  -- on the accelerator device.
  -- 
  -- The result of `runRaw` is both asynchronous uses the constructor `Remote` to
  -- signal that the result is still located on the device rather than the host.
  --
  -- Optionally, a previously compiled blob may be provided, which /may/ be able to
  -- avoid compilation, but this is backend-dependent.
  runRaw :: (Arrays a) => b -> AST.Acc a -> Maybe Blob -> IO (Remote b a)

  -- | Set up a function on the GPU which may be run multiple times.
  runFun :: (Arrays a, Arrays b) => (AST.Acc a -> AST.Acc b) -> Maybe Blob -> Remote b a -> IO (Remote b b)

  -------------------------- Copying and Waiting  -------------------------------

  -- | Take a copy action immediately if the data is available.  This implies `wait`;
  -- if the data is not available `copyToHost` blocks until it becomes ready and is
  -- copied.
  copyToHost   :: Arrays a => b -> Remote b a -> IO a
  -- TODO: Consider adding a separate malloc and overwriting copy.

  -- | Wait until the result is computed, but do not copy it back.  
  wait         :: b -> Remote b a -> IO ()

  -- | If the device uses a separate memory space, allocate memory in the remote
  -- space and transfer the contents of the array to it.
  copyToDevice :: Arrays a => b -> a -> IO (Remote b a)

  -- | Use already-Remote b memory in an Accelerate computation.
  useRemote :: b -> Remote b a -> IO (Acc a)

  --------------------------- Configuration Flags -------------------------------

  -- | Are `copyToDevice` calls complexity O(N) or O(1)?  For example, this might
  -- return True for a discrete GPU and false for an on-chip GPU or CPU backend.
  separateMemorySpace :: b -> Bool

  -- | When asked to produced Blobs, will this backend always go to disk?
  compilesToDisk      :: b -> Bool  

-- | A convenience function.  If a blob is loitering in memory, force it out to disk.
forceToDisk :: Blob -> IO Blob
forceToDisk x@(OnDisk _) = return x
forceToDisk (InMemory p io) = do
  bs <- io
  B.writeFile p bs
  return$ OnDisk p

----------------------------------------------------------------------------------------------------

-- | A portable backend is one that can compile programs to portable binaries, which
-- can be loaded and run without reference to the original `Acc` code.
class Backend b => PortableBackend b where
  -- | Similar to Data.Dynamic.fromDynamic, this only succeeds if the types match.
  runCompiled :: Arrays a => b -> Blob -> IO (Maybe a)

----------------------------------------------------------------------------------------------------

-- | A library backend can be used to produce standalone C code packaging an
-- Accelerate function for external use.  The generated code may have other compile
-- time dependencies, such as CUDA libraries; you must refer to the backend's
-- documentation for details.
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


