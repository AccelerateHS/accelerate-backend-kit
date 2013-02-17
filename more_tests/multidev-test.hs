{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Trafo.Sharing (convertAcc)
import Data.Array.Accelerate.BackendClass
import Foreign.Ptr
import Data.ByteString.Lazy.Char8 as B
import Prelude as P
import Control.Monad
--------------------------------------------------------------------------------

-- Create a list of backends:
data AnyBackend = forall b . Backend b => AnyBackend b
instance Show AnyBackend where
  show (AnyBackend b) = "AnyBackend ("++show b++")"

-- | Likewise we might wish to store Remotes in a backend-agnostic way: Note: this is
--   very touchy.  It's not enough to have 'b' as a type-parameter to Remote, we must
--   also store the backend 'b' itself.
data AnyRemote r = forall b . Backend b => AnyRemote b (Remote b r)
instance Show (AnyRemote r) where
  show (AnyRemote b _) = "<Remote handle for backend "++show b++">"

-- These constructors might well be unexported, and might have state:
data FooBackend = FooBackend Int deriving Show
data BarBackend = BarBackend deriving Show

instance Backend FooBackend where
  -- Here 'remote' objects are just on the Haskell heap:
  type Remote FooBackend r = r
  
  -- Return an empty, useless blob:
  compile _ fp acc = return$ InMemory fp $ return ""
  runRaw _ _ _ = return (error "implement")
  
  separateMemorySpace _ = False
  compilesToDisk _ = False

-- | It will be typical to have a constructor function for an instance of a backend.
mkFooBackend :: String -> IO FooBackend
mkFooBackend someParameters =
  return$ FooBackend 33

--------------------------------------------------------------------------------

instance Backend BarBackend where
  -- Let's say this is a discrete-gpu backend:
  type Remote BarBackend r = Ptr r

  -- Actually write something to disk:
  compile _ fp acc = do
    B.writeFile fp "hello\n"
    return$ OnDisk fp
  runRaw _ _ _ = return (error "implement")

  separateMemorySpace _ = True
  compilesToDisk _ = True

--------------------------------------------------------------------------------

p1 :: Acc (Vector Int)
p1 = generate (index1 10) unindex1

main = do
  fb <- mkFooBackend "yay"

  let ls :: [AnyBackend]
      ls = [AnyBackend fb, AnyBackend BarBackend]

  forM_ (P.zip [1..] ls) $ \ (ix,AnyBackend bkend) -> do
    let file = "./test"++show ix++".blob"
    P.putStrLn$ "  Compiling with backend "++show bkend++" to file "++file
    blob <- compile bkend file (doConvert p1)
    P.putStrLn$ "   -> Resulting blob: "++ show blob
    _ <- forceToDisk blob
    return ()

  typeCheckTest

  return ()

-- | This does nothing, but it's important that it typecheck:
typeCheckTest = do
  fb <- mkFooBackend "yay"
  rem1 <- runRaw fb (doConvert p1) Nothing
  rem2 <- runRaw BarBackend (doConvert p1) Nothing  
  let rem1' :: AnyRemote (Vector Int)
      rem1' = AnyRemote fb (rem1 :: Remote FooBackend (Vector Int))

  -- We might keep a list of remotes, across muliple backends:
  let allRemotes :: [AnyRemote (Vector Int)]
      allRemotes = [rem1', AnyRemote BarBackend rem2]
  print allRemotes
  return ()


-- Set the options for the Accelerate front-end AST conversion:
doConvert = convertAcc True True True
