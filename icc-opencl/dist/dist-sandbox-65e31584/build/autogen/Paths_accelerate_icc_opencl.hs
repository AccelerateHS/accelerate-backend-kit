module Paths_accelerate_icc_opencl (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,13,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/sam/src/accelerate/.cabal-sandbox/bin"
libdir     = "/home/sam/src/accelerate/.cabal-sandbox/lib/x86_64-linux-ghc-7.6.3/accelerate-icc-opencl-0.13.0.0"
datadir    = "/home/sam/src/accelerate/.cabal-sandbox/share/x86_64-linux-ghc-7.6.3/accelerate-icc-opencl-0.13.0.0"
libexecdir = "/home/sam/src/accelerate/.cabal-sandbox/libexec"
sysconfdir = "/home/sam/src/accelerate/.cabal-sandbox/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "accelerate_icc_opencl_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "accelerate_icc_opencl_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "accelerate_icc_opencl_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "accelerate_icc_opencl_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "accelerate_icc_opencl_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
