{-# LANGUAGE DeriveGeneric, CPP #-}
{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Type definitions for metadata annotations to ASTs.
module Data.Array.Accelerate.BackendKit.IRs.Metadata
       (
         -- * Metadata types used to annotate ASTs during compilation.
         ArraySizeEstimate(..), Uses(..), FreeVars(..),
         Stride(..), SubBinds(..), OpInputs(..),

         -- * Convenience function for saving metadata and restoring it later.
         liftMetadata, stampMetadata
         )
       where

import Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S 
import Text.PrettyPrint.GenericPretty (Out, Generic)
import Prelude as P

----------------------------------------------------------------------------------------------------
-- Metadata types:
----------------------------------------------------------------------------------------------------

-- | This datatype records what we know statically about array sizes.
data ArraySizeEstimate =
    KnownSize [Int] -- INNERmost dim at the head of the list.
  | UnknownSize
--   | SmallerThan Var -- We'll add this later
--   | SameAs      Var -- We'll add this later
 deriving (Read, Show, Eq, Generic, Ord)
instance Out ArraySizeEstimate


-- | This datatype is used to count uses of a variable in /array
-- context/ or /scalar context/.  This does not reflect whether the
-- variable itself binds an array or scalar.  For example, an array
-- binding can be used both as a whole array (array context) or within
-- scalar code, where, for example, individual elements are
-- dereferenced.
data Uses = Uses { scalarUses :: Int, arrayUses :: Int }
  deriving (Read, Show, Eq, Generic, Ord)
instance Out Uses

-- | A list of free variables for each kernel's body OR for top-level
--   scalar expressions.
newtype FreeVars = FreeVars [Var]
  deriving (Read, Show, Eq, Generic, Ord)
instance Out FreeVars


-- | The 'stride' for fold and scan operations describes the size of the innermost
-- dimension (NOT segmentation).  This is how far apart /separate/ reductions are in
-- the row-major array.  `StrideAll` means we shouldn't worry about how big the array
-- is, everything goes into a single reduction.
data Stride exp = StrideConst exp
                | StrideAll 
  deriving (Read, Show, Eq, Ord, Generic)
instance Out a => Out (Stride a)


-- | Used for breaking named values referring to tuples down into finer-grained
-- bindings.  This includes both a list of unzipped (detupled) names, and a size.
-- The size is only present for array bindings.
data SubBinds = SubBinds { subnames:: [Var],
                           arrsize :: Maybe TrivialExp }
  deriving (Read, Show, Eq, Generic)
instance Out SubBinds

-- | Working around the limitations of the SimpleAcc `Prog` type.  At one point in
-- the compiler, this decorator is used to encode the (unzipped) arguments to each
-- array operator.  The encoding is a list-of-lists because some array operators
-- (e.g. `FoldSeg`) have multiple logical inputs, each of which gets subdivided
-- during unzipping.
data OpInputs = OpInputs [[Var]]
  deriving (Read, Show, Eq, Generic)
instance Out OpInputs


----------------------------------------

-- | Extract metadata from a program.
liftMetadata :: S.Prog a -> M.Map Var a
liftMetadata Prog{progBinds} =
  M.fromList$ P.map (\(ProgBind v _ dec _) -> (v,dec)) progBinds  

-- | Attach metadata to a program, filling in the default value for any new bindings.
stampMetadata :: M.Map Var a -> a -> S.Prog b -> S.Prog (b,a)
stampMetadata mp deflt prog@Prog{progBinds} =
  prog { progBinds= P.map fn progBinds }
  where
    fn (ProgBind v t d r) =
      let dec = case M.lookup v mp of
                 Just x  -> x
                 Nothing -> deflt
      in ProgBind v t (d,dec) r