{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Array.Accelerate.BackendClass (

  -- * Backends using the fully-typed Accelerate interface
  Backend(..), SomeBackend(SomeBackend),

  -- * Backends using the SimpleAcc AST
  SimpleBackend(..), SomeSimpleBackend(SomeSimpleBackend),

  -- Not ready for primetime yet:
  -- PortableBackend(..), CLibraryBackend(..)

  -- * Constructing and converting backends
  MinimalBackend(..),
  LiftSimpleBackend(LiftSimpleBackend),
  DropBackend(DropBackend),

  -- * Running and timing
  runWith, runWithSimple,
  runTimed, runTimedSimple, AccTiming(..),

  -- * Mutual exclusion between backend actions
  LockedBackend(LockedBackend), LockWhich(..), Locks(..),
  newLockedBackend, newLocks, lockCompileOnly,

  -- * Miscellaneous
  Phantom(Phantom),

) where

-- friends
import Data.Array.Accelerate                                    as A hiding ( (++) )
import Data.Array.Accelerate.BackendKit.CompilerPipeline        ( phase0, phase1, phase2A_no1D )
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc           ( Prog(..), showProgSummary )
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone       ( repackAcc, unpackArray )
import Data.Array.Accelerate.BackendKit.Utils.Helpers           ( (#), dbgPrint )
import Data.Array.Accelerate.Trafo                              ( Phase(..) )
import Data.Array.Accelerate.DynamicAcc2                        as Dyn
import qualified Data.Array.Accelerate.AST                      as AST
import qualified Data.Array.Accelerate.Array.Sugar              as Sug
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as SACC
import qualified Data.Array.Accelerate.BackendKit.SimpleArray   as SA

-- standard libraries
import Prelude                                                  hiding ( rem )
import Control.Concurrent.MVar                                  ( newMVar, withMVar, MVar )
import Data.Char                                                ( isAlphaNum )
import Data.Maybe                                               ( fromMaybe )
import Data.Time.Clock                                          ( getCurrentTime, diffUTCTime )
import qualified Data.Map                                       as M
import Data.Typeable                                            ( eqT, (:~:)(..), Typeable, typeOf )
import System.IO.Unsafe                                         ( unsafePerformIO )
import System.Random                                            ( randomIO )
import qualified Data.ByteString.Lazy                           as B


-- We may want to process already-converted, already-optimized,
-- possibly-transformed programs of the type `AST.Acc`, and our backend should
-- let us. See `runRaw` below:
--

-- For this to be useful it also must be possible to use arrays that are already
-- on the remote side in an Accelerate computation.  Thus `useRemote`, akin to
-- `use`.  Compiling it could be tricky; it would need a new AST node, but it's
-- also backend-specific.
--


-- | Run a complete Accelerate program through the front-end, and the given backend.
--   Optionally takes a name associated with the program.
--
runWith :: (Backend b, Arrays a) => b -> DebugName -> Acc a -> a
runWith bkend _nm prog = unsafePerformIO $ do
  let cvtd = phase0 prog
  remote <- runRaw bkend cvtd Nothing
  copyToHost bkend remote

-- | Version of `runWith` that uses a `SimpleBackend` instance instead.
--
runWithSimple :: (SimpleBackend b, Arrays a) => b -> DebugName -> Acc a -> a
runWithSimple bkend _nm prog = unsafePerformIO $ do
  let cvtd = phase1 $ phase0 prog
  rems <- simpleRunRaw bkend Nothing cvtd Nothing
  accArrs <- mapM (simpleCopyToHost bkend) rems
  return $! repackAcc prog accArrs

-- | A version of `runWith` that also returns timing information.
--
runTimed :: (Backend b, Arrays a) => b -> DebugName -> Phase -> Acc a -> IO (AccTiming, a)
runTimed bkend nm _config prog = do
  (rand::Word64) <- randomIO
  t0     <- getCurrentTime
  let cvtd = phase0 prog
      path = ".blob_"++fromMaybe "" nm++"_"++show rand
  blob   <- compile bkend path cvtd
  t1     <- getCurrentTime
  remote <- runRaw bkend cvtd (Just blob)
  t2     <- getCurrentTime
  res    <- copyToHost bkend remote
  t3     <- getCurrentTime
  let d1 = fromRational$ toRational$ diffUTCTime t1 t0
      d2 = fromRational$ toRational$ diffUTCTime t2 t1
      d3 = fromRational$ toRational$ diffUTCTime t3 t2
  return $! (AccTiming d1 d2 d3, res)

runTimedSimple :: (SimpleBackend b) => b -> DebugName -> Phase -> Prog () -> IO (AccTiming, [SA.AccArray])
runTimedSimple bkend nm _config prog = do
  (rand::Word64) <- randomIO
  t0     <- getCurrentTime
  let path = ".blob_"++fromMaybe "" nm++"_"++show rand
  blob   <- simpleCompile bkend path prog
  t1     <- getCurrentTime
  remts  <- simpleRunRaw bkend nm prog (Just blob)
  t2     <- getCurrentTime
  res    <- mapM (simpleCopyToHost bkend) remts
  t3     <- getCurrentTime
  let d1 = fromRational$ toRational$ diffUTCTime t1 t0
      d2 = fromRational$ toRational$ diffUTCTime t2 t1
      d3 = fromRational$ toRational$ diffUTCTime t3 t2
  return $! (AccTiming d1 d2 d3, res)

-- | A timed run includes compile time, runtime, and copying time.  Both compile time
-- and copying time may be zero if these were not needed.  All times are in seconds.
--
data AccTiming = AccTiming
  { compileTime         :: {-# UNPACK #-} !Double
  , runTime             :: {-# UNPACK #-} !Double
  , copyTime            :: {-# UNPACK #-} !Double
  }
  deriving (Show,Eq,Ord,Read)


-- | An encapsulated Backend about which we know nothing else.  (Like SomeException.)
--
data SomeBackend = forall b . Backend b => SomeBackend b

-- | A low-level interface that abstracts over Accelerate backend code generators and
-- expression evaluation. This takes the internal Accelerate AST representation
-- rather than the surface, HOAS one.  The reason for this is that we may want to
-- process already converted and transformed/optimised programs.
--
class Show b => Backend b where

  -- | The type of a remote handle on device memory. This is class-associated
  -- because different backends may represent device pointers differently.
  --
  -- A value of type `Remote b a` stores data of type `a`, where `(Arrays a)`.
  data Remote b :: * -> *

  -- | A `Blob` as a thing which /may/ help speed up or skip future
  -- computations. For example, this may represent:
  --
  --   - compiled object code for an expression
  --
  --   - an optimised and/or annotated AST containing backend-specific execution
  --     parameters
  --
  -- A value of type `Blob b a` represents a program that returns a
  -- value of type `a`, where `(Arrays a)`.
  data Blob b :: * -> *

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
  compileFun1 :: (Arrays x, Arrays y)
              => b
              -> FilePath
              -> AST.Afun (x -> y)
              -> IO (Blob b (x -> y))

  -- | Run an already-optimized Accelerate program (`AST.Acc`) and leave the
  -- results on the accelerator device.
  --
  -- The result of `runRaw` is both asynchronous (returns immediately)
  -- and uses the constructor `Remote` to signal that the result is
  -- still located on the device rather than the host.
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

  -- The default implementation is inefficient, because it potentially issues a new
  -- compile every time the function is invoked.  It throws away the input blob.
  runRawFun1 b afun _mblob rem = do
    inp <- useRemote b rem
    let applied = AST.Apply afun inp
    runRaw b (AST.OpenAcc applied) Nothing

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

  -- | Inject an (already) remote array into an AST node
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
--
type DebugName = Maybe String


-- | An alternative class to Backend which represents a backend that has the ability
-- to handle the simplified AST (SimpleAcc) directly.
--
-- All methods here are substantially different because in this case we do /not/ have
-- type-level information about the inputs and results of Accelerate computations.
--
class (Show b, Typeable b) => SimpleBackend b where

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
  -- [Internal note: the backend-kit compiler phase1 has already been run on this
  -- input, but not phase2.]
  simpleCompile :: b
                -> FilePath
                -> SACC.Prog ()
                -> IO (SimpleBlob b)

  -- | Similar to `compile` but for functions.  Once compiled, the functions can
  -- be invoked repeatedly on the device side without any additional work on the
  -- host.
  --
  -- Without loss of generality the program passed to this function
  -- takes a single argument.  Of course that argument can be an
  -- arbitrary tuple of arrays of tuples.
  simpleCompileFun1 :: b
                    -> FilePath
                    -> SACC.Fun1 (SACC.Prog ())
                    -> IO (SimpleBlob b)

  -- | Run a simplified Accelerate program and leave the results on
  -- the accelerator device.  The list of results should be equal in
  -- length to the `progResults` field of the input `Prog`.  That is,
  -- one result for each array returned from the computation.
  --
  -- The result of `runRaw` is both asynchronous (returns immediately)
  -- and uses the `SimlpeRemote` to signal that the result is still
  -- located on the device rather than the host.
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
  --   returns leaving the results on the device as well.
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

  -------------------------- Passing in data ------------------------------------

  -- | A program can have Use' nodes, which denote data that will be bound later.
  --   This function accepts a map from Var to AccArray, where the Vars
  --   correspond to the Use' nodes where the data should reside.
  --   A blob is optionally passed in, because we might have compiled this
  --   prog before.

  simpleRunStar :: b
                -> DebugName
                -> SACC.Prog ()
                -> Maybe (SimpleBlob b)
                -> M.Map SACC.Var SACC.AccArray
                -> IO [SimpleRemote b]

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

--------------------------------------------------------------------------------------------

-- | An encapsulated SimpleBackend about which we know nothing else.  (Like SomeException.)
--
data SomeSimpleBackend = forall b . SimpleBackend b => SomeSimpleBackend b
  deriving (Typeable)

-- deriving instance Show SomeSimpleBackend

instance Show SomeSimpleBackend where
  show (SomeSimpleBackend b) = show b

data SomeSimpleRemote = forall b . SimpleBackend b => SomeSimpleRemote b (SimpleRemote b)
data SomeSimpleBlob   = forall b . SimpleBackend b => SomeSimpleBlob   b (SimpleBlob b)

-- | When lifted into the common "supertype", a valid SimpleBackend still remains.
--
-- Actually, this is mainly here as a work-around to a GHC bug [2014.07.06].
--
instance SimpleBackend SomeSimpleBackend where
  type SimpleBlob   SomeSimpleBackend = SomeSimpleBlob
  type SimpleRemote SomeSimpleBackend = SomeSimpleRemote

  simpleCompile (SomeSimpleBackend b) path acc = do
    blb <- simpleCompile b path acc
    return $ SomeSimpleBlob b blb

  simpleRunRaw sb nm acc Nothing = do
    blb <- simpleCompile sb (fromMaybe "" nm) acc
    simpleRunRaw sb nm acc (Just blb)

  simpleRunRaw (SomeSimpleBackend _b) nm acc (Just (SomeSimpleBlob b blb)) = do
    -- Could somehow assert that _b and b are the same.
    rs <- simpleRunRaw b nm acc (Just blb)
    return [ SomeSimpleRemote b r | r <- rs ]

  simpleCopyToHost _ (SomeSimpleRemote b r) = simpleCopyToHost b r

  simpleCopyToDevice (SomeSimpleBackend b) a = do
    r <- simpleCopyToDevice b a
    return $ SomeSimpleRemote b r

  simpleCopyToPeer (SomeSimpleBackend (b1::t1)) (SomeSimpleRemote (b2::t2) r) =
    case eqT :: Maybe (t1 :~: t2) of
     Just Refl -> do r2 <- simpleCopyToPeer b1 r
                     return $ SomeSimpleRemote b2 r2
     Nothing -> error $ "simpleCopyToPeer (SomeSimpleBackend instance): called with differently typed backends: "++
                        show (typeOf b1)++" and "++show (typeOf b2)

  simpleWaitRemote _ (SomeSimpleRemote b r)  = simpleWaitRemote b r
  simpleUseRemote  _ (SomeSimpleRemote b r) = simpleUseRemote  b r
  simpleSeparateMemorySpace (SomeSimpleBackend b) = simpleSeparateMemorySpace b

  -- Do this Later:
  -- simpleCompileFun1 (SomeSimpleBackend b) = simpleCompileFun1 b
  -- simpleRunRawFun1  (SomeSimpleBackend b) = simpleRunRawFun1 b



-- | A type wrapper that "casts" a SimpleBackend into a Backend.
--
--   Discarding type information is easy, so we have a subtyping relation in this
--   direction but not the other.
--
newtype LiftSimpleBackend b = LiftSimpleBackend b
  deriving (Show, Eq, Typeable)


-- newtype SimpleRemotesList b _a = SimpleRemotesList [SimpleRemote b]
-- data SimpleBlobPair    b _a = SimpleBlobPair !(SimpleBlob b) !(SACC.Prog ())
--  type Remote (LiftSimpleBackend b) = (SimpleRemotesList b)
--  type Blob (LiftSimpleBackend b)   = (SimpleBlobPair b)

-- | A `SimpleBackend` makes a perfectly reasonable `Backend`.  The
-- conversion merely drops information.
instance (SimpleBackend b) => Backend (LiftSimpleBackend b) where
  data Remote (LiftSimpleBackend b) _r = LSB_Remote ![SimpleRemote b]
  data Blob   (LiftSimpleBackend b) _r = LSB_Blob !(SimpleBlob b) !(SACC.Prog ())

  compile (LiftSimpleBackend b) path acc = do
     let prog = phase1 acc
     blb <- simpleCompile b path prog
     return $! LSB_Blob blb prog

  compileFun1 (LiftSimpleBackend b) path fn = do
     fn2   <- case fn of
                AST.Alam{}      -> error "LiftSimpleBackend.compileFun1: FINISH ME"
                AST.Abody{}     -> error "LiftSimpleBackend.compileFun1: FINISH ME"
     sblob <- simpleCompileFun1 b path fn2
     return $ LSB_Blob sblob undefined

  runRaw lb acc Nothing = do
     blob <- compile lb "unknown_prog" acc
     runRaw lb acc (Just blob)

  runRaw (LiftSimpleBackend b) _origacc (Just (LSB_Blob blob prog)) = do
     x <- simpleRunRaw b Nothing prog (Just blob)
     return $! LSB_Remote x

  copyToHost (LiftSimpleBackend bk) (LSB_Remote rs :: Remote (LiftSimpleBackend b) a) = do
     arrs <- mapM (simpleCopyToHost bk) rs
     return $! repackAcc (undefined::Acc a) arrs

  copyToDevice (LiftSimpleBackend b) (arr :: a) = do
     let (repr :: Sug.ArrRepr a) = Sug.fromArr arr
         (_ty,accArr,_::Phantom a) = unpackArray repr
     remt <- simpleCopyToDevice b accArr
     return $! LSB_Remote [remt]

  copyToPeer (LiftSimpleBackend b) (LSB_Remote rs) =
    fmap LSB_Remote $ mapM (simpleCopyToPeer b) rs

  waitRemote (LiftSimpleBackend b) (LSB_Remote rs) =
    mapM_ (simpleWaitRemote b) rs

  useRemote (LiftSimpleBackend b) (LSB_Remote rs) = do
    _aexps <- mapM (simpleUseRemote b) rs
    error "FINISHME: useRemote/LiftSimpleBackend: this needs to be completed"

  separateMemorySpace (LiftSimpleBackend b) = simpleSeparateMemorySpace b


-- Can't use GeneralizedNewtypeDeriving directly here due to associated types:
--
instance SimpleBackend b => SimpleBackend (LiftSimpleBackend b) where
  type SimpleRemote (LiftSimpleBackend b) = SimpleRemote b
  type SimpleBlob (LiftSimpleBackend b)   = SimpleBlob b
  simpleCompile (LiftSimpleBackend b) path acc = simpleCompile b path acc
  simpleRunRaw (LiftSimpleBackend b) nm acc mb = simpleRunRaw b nm acc mb
  simpleCopyToHost (LiftSimpleBackend b) r     = simpleCopyToHost b r
  simpleCopyToDevice (LiftSimpleBackend b) a   = simpleCopyToDevice b a
  simpleCopyToPeer (LiftSimpleBackend b) r     = simpleCopyToPeer b r
  simpleWaitRemote (LiftSimpleBackend b) r     = simpleWaitRemote b r
  simpleUseRemote (LiftSimpleBackend b) r      = simpleUseRemote b r
  simpleSeparateMemorySpace (LiftSimpleBackend b) = simpleSeparateMemorySpace b
  simpleCompileFun1 (LiftSimpleBackend b) = simpleCompileFun1 b
  simpleRunRawFun1  (LiftSimpleBackend b) = simpleRunRawFun1 b

  -- type Remote (LiftSimpleBackend b) a = Remote b a
  -- type Blob (LiftSimpleBackend b) a   = Blob b a
  -- compile (LiftSimpleBackend b) path acc = compile b path acc
  -- runRaw (LiftSimpleBackend b) acc mb  = runRaw b acc mb
  -- copyToHost (LiftSimpleBackend b) r   = copyToHost b r
  -- copyToDevice (LiftSimpleBackend b) a = copyToDevice b a
  -- copyToPeer (LiftSimpleBackend b) r   = copyToPeer b r
  -- waitRemote (LiftSimpleBackend b) r   = waitRemote b r
  -- useRemote (LiftSimpleBackend b) r    = useRemote b r
  -- separateMemorySpace (LiftSimpleBackend b) = separateMemorySpace b

--------------------------------------------------------------------------------

-- | In an ideal world this should not be necessary.  All `Backend`s
-- and `SimpleBackend`s should be fully threadsafe.  However, you may
-- come across a backend that has problems
--
data LockedBackend b =
     LockedBackend LockWhich Locks b
  deriving (Show, Eq, Typeable)

-- | Configuration specifying which actions should be mutually exclusive.
--
data LockWhich = LockWhich
  { lockCompile         :: Bool         -- ^ Compiles should not happen during other compiles
  , lockRun             :: Bool         -- ^ Runs should not happen during other runs
  , lockTransfer        :: Bool         -- ^ Transfers should not happen during other transfers
  --, lockAll             :: Bool         -- ^ No actions should happen together
  }
  deriving (Eq,Ord,Show,Read)

-- | The actual (mutable) locks themselves.
--
data Locks = Locks
  { compileLock         :: MVar ()
  , runLock             :: MVar ()
  , transferLock        :: MVar ()
  }
  deriving Eq

instance Show Locks where
  show Locks{} = "<Locks>"

-- | Lock only the compile phase.  This is a common use case.
lockCompileOnly :: LockWhich
lockCompileOnly = LockWhich { lockCompile=True, lockRun=False, lockTransfer=False }

-- | Convert a backend to a locked backend, allocating new locks to protect it.
newLockedBackend :: SimpleBackend b => LockWhich -> b -> IO (LockedBackend b)
newLockedBackend which b = do
  locks <- newLocks
  return $ LockedBackend which locks b

-- | Allocate a set of locks to protect a backend.
newLocks :: IO Locks
newLocks = do
  c <- newMVar ()
  r <- newMVar ()
  t <- newMVar ()
  return (Locks c r t)

maybeLock :: Bool -> MVar () -> IO a -> IO a
maybeLock True  lock action = withMVar lock (\() -> action)
maybeLock False _    action = action

instance SimpleBackend b => SimpleBackend (LockedBackend b) where
  type SimpleRemote (LockedBackend b) = SimpleRemote b
  type SimpleBlob   (LockedBackend b) = SimpleBlob b
  simpleCompile (LockedBackend LockWhich{lockCompile} Locks{compileLock} b) path acc =
    maybeLock lockCompile compileLock $ simpleCompile b path acc

  simpleRunRaw (LockedBackend LockWhich{lockRun} Locks{runLock} b) nm acc mb =
    maybeLock lockRun runLock $ simpleRunRaw b nm acc mb

  simpleCopyToHost (LockedBackend LockWhich{lockTransfer} Locks{transferLock} b) r =
    maybeLock lockTransfer transferLock $ simpleCopyToHost b r
  simpleCopyToDevice (LockedBackend LockWhich{lockTransfer} Locks{transferLock} b) a =
    maybeLock lockTransfer transferLock $ simpleCopyToDevice b a
  simpleCopyToPeer (LockedBackend LockWhich{lockTransfer} Locks{transferLock} b) r =
    maybeLock lockTransfer transferLock $ simpleCopyToPeer b r

  simpleWaitRemote (LockedBackend _ _ b) r     = simpleWaitRemote b r
  simpleUseRemote (LockedBackend _ _ b) r      = simpleUseRemote b r
  simpleSeparateMemorySpace (LockedBackend _ _ b) = simpleSeparateMemorySpace b

  simpleCompileFun1 (LockedBackend LockWhich{lockCompile} Locks{compileLock} b) p f =
    maybeLock lockCompile compileLock $ simpleCompileFun1 b p f
  simpleRunRawFun1  (LockedBackend LockWhich{lockCompile} Locks{compileLock} b) n f mb rs =
    maybeLock lockCompile compileLock $ simpleRunRawFun1 b n f mb rs



----------------------------------------------------------------------------------------------------

-- | A type wrapper that "casts" a Backend to a SimpleBackend.  This
--   is a very tricky business and relies on the `DynamicAcc`
--   conversion module to provide runtime checks that construct the
--   full Accelerate AST.
--
newtype DropBackend b = DropBackend b deriving (Show, Eq, Typeable)

-- | Bridging between the `Backend` and `SimpleBackend` notion of a
-- remote is tricky, because the later is more granular.
-- Specifically, this datatype represents a SLICE of the array leaves
-- of the full result of an Accelerate computation.
--
data SomeRemote b = forall a . (Backend b, Arrays a) =>
                    SomeRemote b LeafSlice (Phantom a) (Remote b a)

data LeafSlice = LeafSlice
  { offsetFromRight     :: {-# UNPACK #-} !Int
  , numLeaves           :: {-# UNPACK #-} !Int
  }

data SomeBlob b = forall a . (Backend b, Arrays a) =>
                  SomeBlob b (AST.Acc a) (Blob b a)

instance (Typeable b, Backend b) => SimpleBackend (DropBackend b) where
  type SimpleRemote (DropBackend b) = SomeRemote b
  type SimpleBlob   (DropBackend b) = SomeBlob b

  simpleCompile (DropBackend b) _path prg0 = do
    let prg = fmap (const ()) $ phase2A_no1D prg0 -- TEMP! When DynamicAcc2 is more complete this becomes unnecessary!!
    dbgPrint 2 $ prg `seq` " [DropBackend] Compiling program via DynamicAcc:\n "++showProgSummary prg
    case Dyn.arrayTypeD (SACC.progType prg) of
      SealedArrayType (_ :: Phantom aty) -> do
        let acc :: Acc aty
            acc = downcastA (Dyn.convertProg prg)
            ast = phase0 acc
        blb <- compile b "" ast
        return $ SomeBlob b ast blb

  simpleRunRaw (DropBackend b) nm prg Nothing = do
    sblb <- simpleCompile (DropBackend b) (fromMaybe "" nm) prg
    simpleRunRaw (DropBackend b) nm prg (Just sblb)

  simpleRunRaw (DropBackend (b::bkend)) _nm prg@Prog{progResults} (Just sblb) = do
    case sblb of
      SomeBlob _b (acc::AST.Acc aty) (blb::Blob bkend aty) -> do
        remt <- runRaw b acc (Just blb)
        let results = SACC.resultNames progResults
            env     = SACC.progToEnv prg
        -- Here we need to SUBDIVIDE the resulting arrays...
        -- but only after they are copied back.
        case [ (v, env#v) | v <- results ] of
         [(_nm,TArray _ _)] ->
             return [SomeRemote b (LeafSlice 0 1) (Phantom::Phantom aty) remt]
         _ -> error "Finishme: DropBackend/simpleRunRaw"


  -- runRaw :: (Arrays a)
  --        => b
  --        -> AST.Acc a
  --        -> Maybe (Blob b a)
  --        -> IO (Remote b a)

  simpleCopyToHost (DropBackend b) (SomeRemote _ _slc (_::Phantom aty) (rem :: Remote b aty)) = do
    hsarr <- copyToHost b rem
    let (repr :: Sug.ArrRepr aty) = Sug.fromArr hsarr
        (_,accArr,_::Phantom aty) = unpackArray repr
    dbgPrint 2 $ " [DropBackend] CopyToHost fetched accArray with dims"++show (SA.arrDim accArr)
                  ++", and sizes: "++show (Prelude.map SA.payloadLength (SA.arrPayloads accArr))
    return $ accArr

  -- simpleCopyToDevice (DropBackend b) a   =
  simpleCopyToPeer (DropBackend b) (SomeRemote _ slc (p::Phantom aty) (rem :: Remote b aty)) = do
    -- FIXME: this copies ALL the data, even if we only care about a slice of it.
    -- We should break it down somehow...
    rem2 <- copyToPeer b rem
    return $ SomeRemote b slc p rem2
  simpleWaitRemote (DropBackend b) (SomeRemote _ _ _ (rem :: Remote b aty)) = do
    waitRemote b rem

  simpleUseRemote (DropBackend b) (SomeRemote _ _slc (_::Phantom aty) (rem :: Remote b aty)) = do
    acc <- useRemote b rem
    _ <- return $ phase1 acc
    error $ "Unfinished:simpleUseRemote/DropBackend: unclear how to finish this, should maybe switch to Prog rather than AExp"

  simpleSeparateMemorySpace (DropBackend b) = separateMemorySpace b

  -- Leaving these off for now:
  -- simpleCompileFun1 (DropBackend b) =
  -- simpleRunRawFun1  (DropBackend b) =


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

-- UNFINISHED: Brainstorming other interfaces:

-- | A portable backend is one that can compile programs to /portable/ binaries.
-- These can be loaded and run without reference to the original `Acc` code.
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
  compileLib :: (Arrays a, Arrays b) => (AST.Acc a -> AST.Acc b) -> B.ByteString


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


-- | Takes a basic "run" function and promotes it to a minimal backend.
--   This provides much less control over decisions, like when to copy, than would a proper
--   instance of the backend class.
--
--   Unfortunately this is NOT the same run function that complete Accelerate
--   backends (e.g. Data.Array.Accelerate.Interpreter) will export, because that one
--   expects the HOAS representation, not the converted one (AST.Acc).
--
newtype MinimalBackend = MinimalBackend (forall a . (Arrays a) => AST.Acc a -> a)
  deriving (Typeable)
-- TODO: Should phase out all uses of this!  It hides compile/run distinctions [2014.07.06].

instance Show MinimalBackend where
  show _ = "<MinimalBackend based on run function>"

-- | A Backend class instance based on MinimalBackend is limited.  It cannot separate
-- out compile and copy time, and it cannot store "Blob" objects on disk.
instance Backend MinimalBackend where
  data Remote MinimalBackend r = MB_Remote !r
  data Blob MinimalBackend  _r = MB_Blob

  compile _ _ _     = return MB_Blob
  compileFun1 _ _ _ = return MB_Blob

  runRaw (MinimalBackend runner) acc _mblob =
    return $! MB_Remote (runner acc)

  copyToHost _ (MB_Remote rm) = return $! rm
  copyToDevice _ a = return $! MB_Remote a
  copyToPeer _ rm = return $! rm

  waitRemote _ _ = return ()
  useRemote _ (MB_Remote r) = return $! phase0 (A.use r)
  separateMemorySpace _ = False -- This is pretty bogus, we have no idea.

