

-- | This module defines some simple utilities for building compilers as chains of passes.
--
--   The reason for representing compilers this way is to enable
--   debugging printout and profiling.  That is, it's better for a
--   compiler to be a structured pipeline of passes, rather than an
--   opaque composition of functions.

module Data.Array.Accelerate.BackendKit.CompilerUtils
       (
         -- * Compiler construction, compiler conventions, and global constants:
--         runPass, runOptPass,
--         shapeName, sizeName, isShapeName, isSizeName,
       )
       where

import           Text.PrettyPrint.GenericPretty (Out(doc))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Debug.Trace        (trace)
import           System.IO.Unsafe   (unsafePerformIO)
import           System.Environment (getEnvironment)


