{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}


import           Data.Array.Accelerate
import qualified Data.Array.Accelerate.AST as AST

import           Data.ByteString

-- We may want to process already-converted, already-optimized,
-- possibly-tranfsormed programs of the type `AST.Acc`, and our backend
-- should let us.  See `runRaw` below:


-- For this to be useful it also must be possible to use arrays that are
-- already on the remote side in an Accelerate computation.  Thus
-- `useRemote`, akin to `use`.  Compiling it could be tricky; it would
-- need a new AST node, but it's also backend-specific.


data Blob a = OnDisk FilePath
            | InMemory (IO ByteString)
  
-- run1 :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> Remote a -> IO (Remote b)
-- (Remote a -> IO (Remote b))


-- | A low-level interface that abstracts over Accelerate backend code generators.
class Backend b where
  -- | The type of a remote handle on device memory.  This is class-associated
  -- because different backends may represent device pointers differently.
  type Remote r

  -- | Compile an already converted/optimized Accelerate program into a binary blob
  -- that can be executed.
  compile :: Arrays a => b -> Maybe (AST.Acc a -> IO (Blob a))

  -- | Expose a compilation option for functions.  Once compiled, the functions can be
  -- invoked repeatedly on the device side without any additional work on the host.
  -- compile1 :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> IO (Blob (), (Remote a -> IO (Remote b)))
  -- compile1 :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> IO (Blob (Remote a -> IO (Remote b)))  
  -- Introduce a FunBlob?

  -- | Run an already-optimized Accelerate program and leave the results on the
  -- accelerator device.  
  -- 
  -- The result of `runRaw` is both asynchronous uses the constructor `Remote` to
  -- signal that the result is still located on the device rather than the host. 
  runRaw :: (Arrays a) => b -> AST.Acc a -> IO (Remote a)

  -- | Run a previously compiled Accelerate program.
  -- runWithBlob :: (Arrays a) => b -> AST.Acc a -> Blob a -> IO (Remote a)
  -- runBlob :: (Arrays a) => b -> Blob a -> IO (Remote (Maybe a))

  -- TODO: Consider adding a separate malloc and overwriting copy.

  -- | Take a copy action immediately if the data is available.  This implies `wait`;
  -- if the data is not available `copyToHost` blocks until it becomes ready and is
  -- copied.
  copyToHost   :: b -> Remote a -> IO a

  -- | Wait until the result is computed, but do not copy it back.  
  wait         :: b -> Remote a -> IO ()

  -- | If the device uses a separate memory space, allocate memory in the remote
  -- space and transfer the contents of the array to it.
  copyToDevice :: b -> Arrays a => a -> IO (Remote a)

  -- | Use already-Remote memory in an Accelerate computation.
  useRemote    :: b -> Remote a -> IO (Acc a)


  -- | Are copies O(N) or O(1)?  For example this might return True for a discrete
  -- GPU and false for an on-chip GPU or CPU backend.
  separateMemorySpace :: b -> Bool

  compilesToDisk :: b -> Bool  



-- | A portable backend is one that can compile programs to portable binaries, which
-- can be loaded and run without reference to the original `Acc` code.
class Backend b => PortableBackend b where
  runCompiled :: b -> Blob a -> Maybe a 

-- data CUDABackend -- = ...
-- data CUDARemote r
-- data Context
-- mkCUDABackend :: Context -CUDABackend
-- instance Backend CUDABackend where 
--    type Remote r = CUDARemote r
--    -- ....

-- Finally, it would be good if `Remote` could satisfy the `Unlift` type
-- class so that we might force part of an array but not all of it.  For
-- example:

--     do let (r1,r2) = unlift remote
--        copyToHost r1

-- Hopefully, it would be possible to run a large computation DAG, and to
-- get back a result computed in the middle long before the end of the
-- computation arrives.  

-- Ok, that's it for now.  One missing piece is that I didn't include
-- `run1` above.  I assume it would need to continue using the surface
-- `Acc` type given its signature:

-- run1 :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> Remote a -> IO (Remote b)

-- But rather than include this as a method of `Backend`, maybe it is
-- better to explicitly provide `compile` and `compileFun` methods?


-- (2) Fixing the unsafe operations (fold/scan/permute)
-- ====================================================

-- Accelerate is presently a non-deterministic programming model, called
-- from pure code and without `unsafe` in the name.  There are basically
-- two solutions to this problem that I'm aware of, both of which involve
-- separating the safe from the unsafe parts.

--  * Introduce an `Acc` type class that abstracts over specific
--    Accelerate type constructors like `AccPure` and `AccIO`.
--  * Leave a single `Acc` type constructor, but place unsafe functions
--    in another module such as `Data.Array.Accelerate.Unsafe`

-- In either case it is desirable to add safe versions of folds and
-- scans.  These should certainly include known-associative folds such as
-- sum and product.  But in the future they may also include
-- topology-guaranteed parallel folds and scans, for example, a parallel
-- fold that guarantees a binary tree topology.



-- Support Defs
-- ------------

-- #ifdef VER1
-- data Remote a
-- data Async a
-- #else
-- mkCUDABackend = undefined
-- #endif

-- run1 = undefined

-- class Remote where


