{-# LANGUAGE DeriveGeneric, CPP #-}
{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Type definitions for metadata annotations to ASTs.
module Data.Array.Accelerate.BackendKit.IRs.Metadata
       (
         -- * Metadata types used to annotate ASTs during compilation.
         ArraySizeEstimate(..), Uses(..), FreeVars(..),
         FoldStrides(FoldStrides)
         )
       where

import Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Var)
import Text.PrettyPrint.GenericPretty (Out, Generic)

----------------------------------------------------------------------------------------------------
-- Metadata types:
----------------------------------------------------------------------------------------------------

-- | This datatype records what we know statically about array sizes.
data ArraySizeEstimate =
    KnownSize [Int]
  | UnknownSize
--   | SmallerThan Var -- We'll add this later
--   | SameAs      Var -- We'll add this later
 deriving (Read, Show, Eq, Generic)
instance Out ArraySizeEstimate


-- | This datatype is used to count uses of a variable in /array
-- context/ or /scalar context/.  This does not reflect whether the
-- variable itself binds an array or scalar.  For example, an array
-- binding can be used both as a whole array (array context) or within
-- scalar code, where, for example, individual elements are
-- dereferenced.
data Uses = Uses { scalarUses :: Int, arrayUses :: Int }
  deriving (Read, Show, Eq, Generic)
instance Out Uses

-- | A list of free variables for each kernel's body OR for top-level
--   scalar expressions.
newtype FreeVars = FreeVars [Var]
  deriving (Read, Show, Eq, Generic)
instance Out FreeVars


-- | Record the stride in the array (i.e. innermost dimension) between separate
--   folds.  This maps each top level array variable that is the result of a fold or
--   scan onto an expression of type TInt.
-- newtype FoldStrides exp = FoldStrides (M.Map Var exp)
newtype FoldStrides exp = FoldStrides (Maybe exp)
  deriving (Read, Show, Eq, Generic)
instance Out a => Out (FoldStrides a)
