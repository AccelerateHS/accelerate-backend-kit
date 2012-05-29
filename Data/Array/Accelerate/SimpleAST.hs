{-# LANGUAGE DeriveGeneric, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- TEMP: for UArray Read instance:
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances #-}
module Data.Array.Accelerate.SimpleAST  
   ( 
     -- * The types making up Accelerate ASTs:
     AExp(..), AFun(..), 
     Exp(..), Fun(..), 
     Type(..), Const(..),
     Prim(..), NumPrim(..), IntPrim(..), FloatPrim(..), ScalarPrim(..), BoolPrim(..), OtherPrim(..),
     Boundary(..),
     Var,
          
     -- * Runtime Array data representation.
     AccArray(..), ArrayPayload(..), 
     
     -- * Slice representation
     SliceType(..), SliceComponent(..),
           
     -- * Helper routines and predicates:
     var, primArity, constToInteger,
     isIntType, isFloatType, isNumType, 
     isIntConst, isFloatConst, isNumConst
    )   
 where

-- import Data.Array.Accelerate.SimpleArray (AccArray)

import           Debug.Trace
import           Data.Int
import           Data.Word
import           Data.Array.Unboxed as U
import qualified Data.Array.Unsafe as Un
import qualified Data.Array.MArray as MA
import qualified Data.Array.IO     as IA
import           Foreign.C.Types 
import           Pretty (text) -- ghc api
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import           System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map          as M
--------------------------------------------------------------------------------
-- Prelude: Pick a simple representation of variables (interned symbols)
--------------------------------------------------------------------------------
-- Several modules offer this, with varying problems:
----------------------------
#define USE_SYMBOL
#ifdef USE_STRINGTABLE
-- 'stringtable-atom' package:
-- I'm getting some segfaults here [2012.05.19];
import StringTable.Atom
var = toAtom
type Var = Atom
----------------------------
#elif defined(USE_SIMPLEATOM)
-- 'simple-atom' package:
import Data.Atom.Simple
var = intern
type Var = Symbol
----------------------------
#elif defined(USE_SYMBOL)
-- 'symbol' package
import Data.Symbol
var = intern
type Var = Symbol 
instance Show Symbol where 
 show = unintern
instance Read Symbol where 
-- NOTE - this package would seem to be unsafe because the Symbol type
-- constructor is exported.
#endif
  
var :: String -> Var
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Accelerate Array-level Expressions
--------------------------------------------------------------------------------

-- | Array-level expressions
data AExp = 
    Vr Var -- Array variable bound by a Let.
  | Unit Exp -- Turn an element into a singleton array
    -- Let is used for common subexpression elimination
  | Let  Var Type AExp AExp    -- Let Var Type RHS Body
  | ArrayTuple [AExp]          -- Tuple of arrays.
  | TupleRefFromRight Int AExp 
    
  | Apply AFun AExp              -- Function $ Argument
  | Cond Exp AExp AExp           -- Array level if statements
  | Use  Type AccArray           -- A real live ARRAY goes here!
  | Generate Type Exp Fun        -- Generate Function Array, very similar to map
  | Replicate SliceType Exp AExp -- Replicate array across one or more dimensions.
  | Index     SliceType AExp Exp -- Index a sub-array (slice).
                                 -- Index sliceIndex Array SliceDims
  | Map      Fun AExp            -- Map Function Array
  | ZipWith  Fun AExp AExp       -- ZipWith Function Array1 Array2
  | Fold     Fun Exp AExp        -- Fold Function Default Array
  | Fold1    Fun AExp            -- Fold1 Function Array
  | FoldSeg  Fun Exp AExp AExp   -- FoldSeg Function Default Array 'Segment Descriptor'
  | Fold1Seg Fun     AExp AExp   -- FoldSeg Function         Array 'Segment Descriptor'
  | Scanl    Fun Exp AExp        -- Scanl  Function InitialValue LinearArray
  | Scanl'   Fun Exp AExp        -- Scanl' Function InitialValue LinearArray
  | Scanl1   Fun     AExp        -- Scanl  Function              LinearArray
  | Scanr    Fun Exp AExp        -- Scanr  Function InitialValue LinearArray
  | Scanr'   Fun Exp AExp        -- Scanr' Function InitialValue LinearArray
  | Scanr1   Fun     AExp        -- Scanr  Function              LinearArray
  | Permute  Fun AExp Fun AExp   -- Permute CombineFun DefaultArr PermFun SourceArray
  | Backpermute Exp Fun AExp     -- Backpermute ResultDimension   PermFun SourceArray
  | Reshape     Exp     AExp     -- Reshape Shape Array
  | Stencil  Fun Boundary AExp
  | Stencil2 Fun Boundary AExp Boundary AExp -- Two source arrays/boundaries
 deriving (Read,Show,Eq,Generic)

-- | Array-level functions.
data AFun = ALam [(Var,Type)] AExp
 deriving (Read,Show,Eq,Generic)

-- | Boundary condition specification for stencil operations.
data Boundary = Clamp               -- ^clamp coordinates to the extent of the array
              | Mirror              -- ^mirror coordinates beyond the array extent
              | Wrap                -- ^wrap coordinates around on each dimension
              | Constant Const      -- ^use a constant value for outlying coordinates 
 deriving (Read,Show,Eq,Generic)
          
          
--------------------------------------------------------------------------------
-- Accelerate Scalar Expressions and Functions
--------------------------------------------------------------------------------

-- | Scalar functions
data Fun = Lam [(Var,Type)] Exp
 deriving (Read,Show,Eq,Generic)

-- | Scalar expressions
data Exp = 
    EVr Var -- Variable bound by a Let.
  | ELet Var Type Exp Exp    -- ELet Var Type RHS Body
  -- ELet is used for common subexpression elimination
  | EPrimApp Prim [Exp]  -- *Any* primitive scalar function
  | ETuple [Exp]
  | EConst Const
   -- [2012.04.02] I can't presently compute the length from the TupleIdx.
   --  | EPrj Int Int Exp  -- n m e : Project the nth field of an m-length tuple.
  | ETupProjectFromRight Int Exp  -- Project the nth field FROM THE RIGHT end of the tuple.  
  | EIndex [Exp] -- Index into a multi-dimensional array:
  | EIndexAny 
  -- I'm not sure I'm following this -- 
  -- Accelerate would seem to allow run-time CONSING of indices:
  -- In a staged model like this shouldn't we be able to get rid of that at metaprogram eval time?  
  | EIndexConsDynamic Exp Exp
  | EIndexHeadDynamic Exp 
  | EIndexTailDynamic Exp 
   -- Conditional expression (non-strict in 2nd and 3rd argument):
  | ECond Exp Exp Exp
   -- Project a single scalar from an array,
   -- the array expression can not contain any free scalar variables:
  | EIndexScalar AExp Exp 
   -- Get the shape of an Array:
   -- The array expression can not contain any free scalar variables
  | EShape AExp
   -- Number of elements of a shape
  | EShapeSize Exp 
 deriving (Read,Show,Eq,Generic)


-- | Constants embedded within Accelerate programs (i.e. in the AST).
data Const = I Int  | I8 Int8  | I16 Int16  | I32 Int32  | I64 Int64
           | W Word | W8 Word8 | W16 Word16 | W32 Word32 | W64 Word64
           | F Float | D Double | C Char | B Bool
           | Tup [Const]
            -- C types, rather annoying:
           | CF CFloat   | CD CDouble 
           | CS  CShort  | CI  CInt  | CL  CLong  | CLL  CLLong
           | CUS CUShort | CUI CUInt | CUL CULong | CULL CULLong
           | CC  CChar   | CSC CSChar | CUC CUChar 
 deriving (Read,Show,Eq,Generic)


--------------------------------------------------------------------------------
-- Accelerate Primitive Operations
--------------------------------------------------------------------------------

-- | A datatype that includes all primitives supported by Accelerate.
data Prim = NP NumPrim
          | IP IntPrim
          | FP FloatPrim
          | SP ScalarPrim
          | BP BoolPrim
          | OP OtherPrim
  deriving (Read,Show,Eq,Ord,Generic)
          
-- | Primitives that operate on /all/ numeric types.
--   Neg/Abs/Sig are unary:
data NumPrim = Add | Sub | Mul | Neg | Abs | Sig
  deriving (Read,Show,Eq,Ord,Generic)

-- | Primitive integral-only operations.
-- All binops except BNot, shifts and rotates take an Int constant as second arg:
data IntPrim = Quot | Rem | IDiv | Mod | 
               BAnd | BOr | BXor | BNot | BShiftL | BShiftR | BRotateL | BRotateR
  deriving (Read,Show,Eq,Ord,Generic)

-- | Primitive floating point-only operations.
data FloatPrim = 
      -- Unary:
      Recip | Sin | Cos | Tan | Asin | Acos | Atan | Asinh | Acosh | Atanh | ExpFloating | Sqrt | Log |
      -- Binary:                  
      FDiv | FPow | LogBase | Atan2 | Truncate | Round | Floor | Ceiling
  deriving (Read,Show,Eq,Ord,Generic)
           
-- | Relational and equality operators
data ScalarPrim = Lt | Gt | LtEq | GtEq | Eq | NEq | Max | Min
  deriving (Read,Show,Eq,Ord,Generic)

data BoolPrim = And | Or | Not
  deriving (Read,Show,Eq,Ord,Generic)

data OtherPrim = Ord | Chr | BoolToInt | FromIntegral
  deriving (Read,Show,Eq,Ord,Generic)


-- | This is a table of primitive arities.
primArity :: Prim -> Int 
-- Note: this would be safer with a normal case expression, but would be rather long:
primArity p = mp M.! p
 where 
  mp = M.fromList $ 
   zip binaries (repeat 2) ++
   zip unaries  (repeat 1)
  binaries = 
    [BP And, BP Or] ++
    [NP Add, NP Mul, IP BNot] ++
    map IP [Quot, Rem, IDiv, Mod, BOr, BXor, BShiftL, BShiftR, BRotateL, BRotateR] ++
    map FP [FDiv, FPow, LogBase, Atan2, Truncate, Round, Floor, Ceiling] ++
    map SP [Lt, Gt, LtEq, GtEq, Eq, NEq, Max, Min]
  unaries =   
    [BP Not] ++ 
    map OP [Ord, Chr, BoolToInt, FromIntegral] ++
    map NP [Neg, Abs, Sig] ++ 
    map FP [Recip, Sin, Cos, Tan, Asin, Acos, Atan, Asinh, Acosh, Atanh, ExpFloating, Sqrt, Log]

--------------------------------------------------------------------------------
-- Accelerate Types
--------------------------------------------------------------------------------

-- | Accelerate types.
data Type = TTuple [Type]
          | TArray Dims Type
          | TInt   | TInt8  | TInt16  | TInt32  | TInt64
          | TWord  | TWord8 | TWord16 | TWord32 | TWord64
          | TFloat | TDouble | TChar | TBool
          -- C types (rather annoying):
          | TCFloat  | TCDouble 
          | TCShort  | TCInt   | TCLong  | TCLLong
          | TCUShort | TCUInt  | TCULong | TCULLong
          | TCChar   | TCSChar | TCUChar 
 deriving (Read,Show,Eq,Generic)

type Dims = Int


-- | Slices of arrays.  These have a length matching the
-- dimensionality of the slice.  
-- 
-- The resulting lists read right-to-left, in the OPPOSITE
-- order that one would write `(Z :. 3 :. 4 :. All)` in the source code;
-- i.e. that particular example would translate to `[All, Fixed, Fixed]`.
--
-- The result is that the "fastest varying" dimension is on the left
-- in this representation.
type SliceType      = [SliceComponent]
data SliceComponent = Fixed | All
  deriving (Eq,Show,Read,Generic)

-- TEMP / OLD:
-- They read left-to-right, in the same
-- order that one would write `(Z :. 3 :. 4 :. All)` in the source code.
-- That particular example would translate to `[Fixed, Fixed, All]`.

-------------------------------------------------------------------------------
-- Accelerate Runtime Array Data
--------------------------------------------------------------------------------

-- | This is a complete Accelerate array living on the Haskell heap.
--   It needs to handle different forms of scalar data (different
--   payloads).  
--  
--   Note, this is a different presentation of the same data as
--   contained in a `Data.Array.Accelerate.Array`.  Going with the
--   theme of "SimpleAST", the idea is to provide access in a form
--   that doesn't require complex types.  However, while simple in
--   that respect, this representation is also a pain to work with
--   because `ArrayPayload` is a large sum type.
-- 
--   Arrays of tuples are still "unzipped" in this representation
--   (i.e. represented as tuples of arrays).  The dimensions are
--   represented as a simple list of integers.  For example, [2,3,4]
--   would be dimensions for a three dimensional array.
-- 
--   Invariant -- all payload arrays should be the same length, and:
--   > sum (arrDim a) == length (arrPayloads a !! i)
data AccArray = AccArray { arrDim :: [Int], arrPayloads :: [ArrayPayload] }
 deriving (Show, Read, Eq)

-- | This is a single, contiguous batch of elements, representing one
--   tuple-component of the contents of an Accelerate array.
data ArrayPayload = 
    ArrayPayloadInt    (RawData Int)
  | ArrayPayloadInt8   (RawData Int8)
  | ArrayPayloadInt16  (RawData Int16)
  | ArrayPayloadInt32  (RawData Int32)   
  | ArrayPayloadInt64  (RawData Int64)
  | ArrayPayloadWord   (RawData Word)
  | ArrayPayloadWord8  (RawData Word8)
  | ArrayPayloadWord16 (RawData Word16)
  | ArrayPayloadWord32 (RawData Word32)   
  | ArrayPayloadWord64 (RawData Word64)
  | ArrayPayloadFloat  (RawData Float)
  | ArrayPayloadDouble (RawData Double)
  | ArrayPayloadChar   (RawData Char)
  | ArrayPayloadBool   (RawData Word8) -- Word8's represent bools.
--  | ArrayPayloadUnit -- Dummy placeholder value.
--  
-- TODO -- Add C-types.  But as of this date [2012.05.21], Accelerate
-- support for these types is incomplete, so we omit them here as well.
--   
-- TODO: UArray doesn't offer cast like IOArray.  It would be nice
-- to make all arrays canonicalized to a data buffer of Word8's:
 deriving (Show, Read, Eq)
  
-- | This is our Haskell representation of raw, contiguous data.
-- Subject to change in the future depending on what internal
-- representation the Accelerate front-end uses.
type RawData e = UArray Int e
   
-------------------------------------------------------------------------------
-- Shape representation:
--------------------------------------------------------------------------------

-- Shapes are represented at runtime by tuples of integers.  For example:
--   1D shape: (I 5)
--   2D shape: Tup [I 2, I 3]
--   3D shape: Tup [I 2, I 3, I 4]
-- etc.


--------------------------------------------------------------------------------
-- Convenience functions for dealing with large sum types.
--------------------------------------------------------------------------------

-- | Is the type numeric, rather than, for example, an array, tuple,
-- boolean or character.  Note that C characters are considered
-- numeric.
isNumType ty = isIntType ty || isFloatType ty

-- | Is the scalar type integral?  This includes words as well as
-- signed ints as well as C types.
isIntType ty =
  case ty of {
    TInt  ->t;     TInt8 ->t;    TInt16  ->t;  TInt32  ->t;  TInt64 ->t; 
    TWord  ->t;    TWord8 ->t;   TWord16  ->t; TWord32  ->t; TWord64 ->t; 
    TCShort  ->t;  TCInt   ->t;  TCLong  ->t;  TCLLong ->t; 
    TCUShort ->t;  TCUInt  ->t;  TCULong ->t;  TCULLong ->t;
     _ -> False
  }
 where t = True

isFloatType ty = 
  case ty of {
    TFloat  ->t; TDouble ->t; 
    TCFloat ->t; TCDouble ->t;
    _ -> False  
  }
 where t = True

-- | Is it a numeric constant representing an exact integer?  This
-- includes words as well as signed ints as well as C types.
isIntConst c =
  case c of {
    I _ ->t;    I8 _ ->t;    I16 _  ->t;  I32 _  ->t;  I64 _ ->t; 
    W _ ->t;    W8 _ ->t;    W16 _  ->t;  W32 _  ->t;  W64 _ ->t;     
    CS _ ->t;  CI _ ->t;  CL _ ->t;  CLL _ ->t; 
    CUS _ ->t;  CUI _ ->t;  CUL _ ->t;  CULL _ ->t;
     _ -> False
  }
 where t = True

-- | Is the constant an inexact floating point number (of any precision)?
isFloatConst c = 
  case c of {
    F _ ->t;  D _ ->t; 
    CF _ ->t; CD _ ->t;
    _ -> False  
  }
 where t = True

-- | Is the constant numeric, rather than a tuple, boolean or
-- character.  Note that C characters are considered numeric.
isNumConst ty = isIntConst ty || isFloatConst ty


-- | Convert any const satisfying `isIntConst` into a Haskell
-- `Integer` value.
constToInteger c = 
  case c of 
    I   i -> toInteger i
    I8  i -> toInteger i
    I16 i -> toInteger i
    I32 i -> toInteger i
    I64 i -> toInteger i
    W   i -> toInteger i
    W8  i -> toInteger i
    W16 i -> toInteger i
    W32 i -> toInteger i
    W64 i -> toInteger i
    CS  i -> toInteger i
    CI  i -> toInteger i
    CL  i -> toInteger i 
    CLL i -> toInteger i 
    CUS i -> toInteger i 

--------------------------------------------------------------------------------
-- Boilerplate for generic pretty printing:

instance Out Type
instance Out Fun
instance Out Exp
instance Out AExp
instance Out AFun
instance Out Const
instance Out Prim
instance Out NumPrim
instance Out IntPrim
instance Out FloatPrim
instance Out ScalarPrim
instance Out BoolPrim
instance Out OtherPrim
instance Out Boundary
instance Out SliceComponent

instance Out Var    where docPrec _ = text . show; doc = docPrec 0 
instance Out Int8   where docPrec _ = text . show; doc = docPrec 0 
instance Out Int16  where docPrec _ = text . show; doc = docPrec 0
instance Out Int32  where docPrec _ = text . show; doc = docPrec 0 
instance Out Int64  where docPrec _ = text . show; doc = docPrec 0
instance Out Word   where docPrec _ = text . show; doc = docPrec 0 
instance Out Word8  where docPrec _ = text . show; doc = docPrec 0 
instance Out Word16 where docPrec _ = text . show; doc = docPrec 0
instance Out Word32 where docPrec _ = text . show; doc = docPrec 0 
instance Out Word64 where docPrec _ = text . show; doc = docPrec 0
instance Out CFloat  where docPrec _ = text . show; doc = docPrec 0 
instance Out CDouble where docPrec _ = text . show; doc = docPrec 0 
instance Out CShort  where docPrec _ = text . show; doc = docPrec 0
instance Out CInt    where docPrec _ = text . show; doc = docPrec 0 
instance Out CLong   where docPrec _ = text . show; doc = docPrec 0                          
instance Out CLLong  where docPrec _ = text . show; doc = docPrec 0 
instance Out CUShort where docPrec _ = text . show; doc = docPrec 0
instance Out CUInt   where docPrec _ = text . show; doc = docPrec 0 
instance Out CULong  where docPrec _ = text . show; doc = docPrec 0
instance Out CULLong where docPrec _ = text . show; doc = docPrec 0 
instance Out CChar   where docPrec _ = text . show; doc = docPrec 0 
instance Out CSChar  where docPrec _ = text . show; doc = docPrec 0
instance Out CUChar  where docPrec _ = text . show; doc = docPrec 0 

-- TODO: Get proper pretty printing going here:
instance Out AccArray where docPrec _ = text . show; doc = docPrec 0

-- Why is this one not included in the array package?:
instance (Read elt, U.IArray UArray elt) => Read (U.UArray Int elt) where
    readsPrec p = readParen (p > 9)
           (\r -> [(U.array b as :: U.UArray Int elt, u) | 
                   ("array",s) <- lex r,
                   (b,t)       <- reads s,
                   (as :: [(Int,elt)],u) <- reads t ])

test :: UArray Int Int
test = read "array (1,5) [(1,200),(2,201),(3,202),(4,203),(5,204)]" :: U.UArray Int Int



----------------------------------------------------------------------------------------------------

-- Note: an alternate approach to the large sum of payload types would
-- be to cast them all to a UArray of bytes.  There is not direct
-- support for this in the UArray module, but we could accomplish it
-- with something like the following:
castUArray :: forall ix a b . (Ix ix, IArray UArray a, IArray UArray b, 
                               IA.MArray IA.IOUArray a IO, IA.MArray IA.IOUArray b IO)
           => UArray ix a -> UArray ix b
castUArray uarr = unsafePerformIO $ 
  do thawed :: IA.IOUArray ix a <- Un.unsafeThaw uarr
     cast   :: IA.IOUArray ix b <- Un.castIOUArray thawed
     froze  :: UArray ix b      <- Un.unsafeFreeze cast
     return froze

-- Like Data.Vector.generate, but for `UArray`s.  Unfortunately, this
-- requires extra class constraints for `IOUArray` as well.
uarrGenerate :: (IArray UArray a, IA.MArray IA.IOUArray a IO)
             => Int -> (Int -> a) -> UArray Int a
uarrGenerate len fn = unsafePerformIO $ 
  do marr :: IA.IOUArray Int a <- MA.newArray_ (0,len)
     let loop (-1) = Un.unsafeFreeze marr
         loop i = do MA.writeArray marr i (fn i)
                     loop (i-1)
     loop (len-1)

tracePrint s x = trace (s++show x) x    