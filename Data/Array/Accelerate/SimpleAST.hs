{-# LANGUAGE DeriveGeneric, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- TEMP: for UArray Read instance:
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, FlexibleContexts #-}
module Data.Array.Accelerate.SimpleAST  
   ( 
     -- * The types making up Accelerate ASTs:
     AExp(..), AFun(..), 
     Exp(..), Fun(..), 
     Type(..), Const(..),
     Prim(..), NumPrim(..), FloatPrim(..), ScalarPrim(..), BoolPrim(..), OtherPrim(..),
     Boundary(..),
     Var,
     
     -- * Runtime Array data representation.
     SliceType(..), SliceComponent(..),
     AccArray(..), ArrayPayload(..), 
     payloadLength, applyToPayload, applyToPayload2, applyToPayload3, 
     
     -- * Helper routines and predicates:
     var, isIntType, isFloatType
    )   
 where

import Debug.Trace
import Data.Int
import Data.Word
import Data.Array.Unboxed as U
import Foreign.C.Types 
import Pretty (text) -- ghc api
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
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
   -- I'm not sure I'm follwing this -- Accelerate would seem to allow run-time CONSING of indices:
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
            -- Special constants:
           | MinBound | MaxBound | Pi
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
  deriving (Read,Show,Eq,Generic)
          
-- | Primitives that operate on /all/ numeric types.
--   Neg/Abs/Sig are unary:
data NumPrim = Add | Mul | Neg | Abs | Sig
  deriving (Read,Show,Eq,Generic)

-- | Primitive integral-only operations.
-- All binops except BNot, shifts and rotates take an Int constant as second arg:
data IntPrim = Quot | Rem | IDiv | Mod | 
               BAnd | BOr | BXor | BNot | BShiftL | BShiftR | BRotateL | BRotateR
  deriving (Read,Show,Eq,Generic)

-- | Primitive floating point-only operations.
data FloatPrim = 
      -- Unary:
      Recip | Sin | Cos | Tan | Asin | Acos | Atan | Asinh | Acosh | Atanh | ExpFloating | Sqrt | Log |
      -- Binary:                  
      FDiv | FPow | LogBase | Atan2 | Truncate | Round | Floor | Ceiling
  deriving (Read,Show,Eq,Generic)
           
-- | Relational and equality operators
data ScalarPrim = Lt | Gt | LtEq | GtEq | Eq | NEq | Max | Min
  deriving (Read,Show,Eq,Generic)

data BoolPrim = And | Or | Not
  deriving (Read,Show,Eq,Generic)

data OtherPrim = Ord | Chr | BoolToInt | FromIntegral
  deriving (Read,Show,Eq,Generic)


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

isIntType ty =
  case ty of {
    TInt  ->t;     TInt8 ->t;    TInt16  ->t;  TInt32  ->t;  TInt64 ->t; 
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

-- | Slices of arrays.  These have a length matching the
-- dimensionality of the slice.  
-- 
-- The resulting lists read right-to-left, in the OPPOSITE
-- order that one would write `(Z :. 3 :. 4 :. All)` in the source code;
-- i.e. that particular example would translate to `[All, Fixed, Fixed]`.
--
type SliceType      = [SliceComponent]
data SliceComponent = Fixed | All
  deriving (Eq,Show,Read,Generic)

-- TEMP / OLD:
-- The read left-to-right, in the same
-- order that one would write `(Z :. 3 :. 4 :. All)` in the source code.
-- That particular example would translate to `[Fixed, Fixed, All]`.


-------------------------------------------------------------------------------
-- Accelerate Runtime Array Data
--------------------------------------------------------------------------------

-- | This is a complete Accelerate array living on the Haskell heap.
--   It needs to handle different forms of scalar data (different payloads).
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
  | ArrayPayloadUnit -- Dummy placeholder value.
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


-- | How many elements are in the payload?  This handles the annoying
--   large case dispatch on element type.
payloadLength :: ArrayPayload -> Int
payloadLength payl =
  case payl of 
    ArrayPayloadUnit       -> 0
    ArrayPayloadInt    arr -> arrLen arr
    ArrayPayloadInt8   arr -> arrLen arr
    ArrayPayloadInt16  arr -> arrLen arr
    ArrayPayloadInt32  arr -> arrLen arr
    ArrayPayloadInt64  arr -> arrLen arr
    ArrayPayloadWord   arr -> arrLen arr
    ArrayPayloadWord8  arr -> arrLen arr
    ArrayPayloadWord16 arr -> arrLen arr
    ArrayPayloadWord32 arr -> arrLen arr
    ArrayPayloadWord64 arr -> arrLen arr
    ArrayPayloadFloat  arr -> arrLen arr
    ArrayPayloadDouble arr -> arrLen arr
    ArrayPayloadChar   arr -> arrLen arr
    ArrayPayloadBool   arr -> arrLen arr
 where    
   arrLen arr = let (st,en) = U.bounds arr in en - st      

-- | Apply a generic transformation to the Array Payload irrespective of element type.
applyToPayload :: (forall a . UArray Int a -> UArray Int a) -> ArrayPayload -> ArrayPayload
applyToPayload fn payl = applyToPayload2 (\ a _ -> fn a) payl
  -- case payl of 
  --   ArrayPayloadInt    arr -> ArrayPayloadInt    (fn arr)
  --   ArrayPayloadInt8   arr -> ArrayPayloadInt8   (fn arr)
  --   ArrayPayloadInt16  arr -> ArrayPayloadInt16  (fn arr)
  --   ArrayPayloadInt32  arr -> ArrayPayloadInt32  (fn arr) 
  --   ArrayPayloadInt64  arr -> ArrayPayloadInt64  (fn arr)
  --   ArrayPayloadWord   arr -> ArrayPayloadWord   (fn arr)
  --   ArrayPayloadWord8  arr -> ArrayPayloadWord8  (fn arr) 
  --   ArrayPayloadWord16 arr -> ArrayPayloadWord16 (fn arr)
  --   ArrayPayloadWord32 arr -> ArrayPayloadWord32 (fn arr)
  --   ArrayPayloadWord64 arr -> ArrayPayloadWord64 (fn arr)
  --   ArrayPayloadFloat  arr -> ArrayPayloadFloat  (fn arr)
  --   ArrayPayloadDouble arr -> ArrayPayloadDouble (fn arr)
  --   ArrayPayloadChar   arr -> ArrayPayloadChar   (fn arr)
  --   ArrayPayloadBool   arr -> ArrayPayloadBool   (fn arr) -- Word8's represent bools.

-- | This is similar to `applyToPayload`, but also provides the ability for
-- the function passed in to inspect elements in the input array in a
-- generic fashion (as Const) type.
applyToPayload2 :: (forall a . UArray Int a -> (Int -> Const) -> UArray Int a) -> ArrayPayload -> ArrayPayload
applyToPayload2 fn payl = 
  case payl of 
    ArrayPayloadUnit       -> ArrayPayloadUnit
    ArrayPayloadInt    arr -> ArrayPayloadInt    (fn arr (\i -> I (arr U.! i)))
    ArrayPayloadInt8   arr -> ArrayPayloadInt8   (fn arr (\i -> I8 (arr U.! i)))
    ArrayPayloadInt16  arr -> ArrayPayloadInt16  (fn arr (\i -> I16 (arr U.! i)))
    ArrayPayloadInt32  arr -> ArrayPayloadInt32  (fn arr (\i -> I32 (arr U.! i))) 
    ArrayPayloadInt64  arr -> ArrayPayloadInt64  (fn arr (\i -> I64 (arr U.! i)))
    ArrayPayloadWord   arr -> ArrayPayloadWord   (fn arr (\i -> W (arr U.! i)))
    ArrayPayloadWord8  arr -> ArrayPayloadWord8  (fn arr (\i -> W8 (arr U.! i))) 
    ArrayPayloadWord16 arr -> ArrayPayloadWord16 (fn arr (\i -> W16 (arr U.! i)))
    ArrayPayloadWord32 arr -> ArrayPayloadWord32 (fn arr (\i -> W32 (arr U.! i)))
    ArrayPayloadWord64 arr -> ArrayPayloadWord64 (fn arr (\i -> W64 (arr U.! i)))
    ArrayPayloadFloat  arr -> ArrayPayloadFloat  (fn arr (\i -> F (arr U.! i)))
    ArrayPayloadDouble arr -> ArrayPayloadDouble (fn arr (\i -> D (arr U.! i)))
    ArrayPayloadChar   arr -> ArrayPayloadChar   (fn arr (\i -> C (arr U.! i)))
    ArrayPayloadBool   arr -> ArrayPayloadBool -- Word8's represent bools
                              (fn arr (\i -> case arr U.! i of
                                               0 -> B False 
                                               _ -> B True))

-- | This version allows the payload to be rebuilt as a list of Const,
--    which must all be the same type as the input.
applyToPayload3 :: (Int -> (Int -> Const) -> [Const]) -> ArrayPayload -> ArrayPayload
-- TODO!! The same-type-as-input restriction could be relaxed.
applyToPayload3 fn payl = 
  let len = payloadLength payl in
  tracePrint "\napplyToPayload3: CONVERTED: "$
  case payl of 
    ArrayPayloadUnit       -> ArrayPayloadUnit
    ArrayPayloadInt    arr -> ArrayPayloadInt    (fromL (map unI  $ fn len (\i -> I   (arr U.! i))))
    ArrayPayloadInt8   arr -> ArrayPayloadInt8   (fromL (map unI8 $ fn len (\i -> I8  (arr U.! i))))
    ArrayPayloadInt16  arr -> ArrayPayloadInt16  (fromL (map unI16$ fn len (\i -> I16 (arr U.! i))))
    ArrayPayloadInt32  arr -> ArrayPayloadInt32  (fromL (map unI32$ fn len (\i -> I32 (arr U.! i))))
    ArrayPayloadInt64  arr -> ArrayPayloadInt64  (fromL (map unI64$ fn len (\i -> I64 (arr U.! i))))
    ArrayPayloadWord   arr -> ArrayPayloadWord   (fromL (map unW  $ fn len (\i -> W   (arr U.! i))))
    ArrayPayloadWord8  arr -> ArrayPayloadWord8  (fromL (map unW8 $ fn len (\i -> W8  (arr U.! i))))
    ArrayPayloadWord16 arr -> ArrayPayloadWord16 (fromL (map unW16$ fn len (\i -> W16 (arr U.! i))))
    ArrayPayloadWord32 arr -> ArrayPayloadWord32 (fromL (map unW32$ fn len (\i -> W32 (arr U.! i))))
    ArrayPayloadWord64 arr -> ArrayPayloadWord64 (fromL (map unW64$ fn len (\i -> W64 (arr U.! i))))
    ArrayPayloadFloat  arr -> ArrayPayloadFloat  (fromL (map unF  $ fn len (\i -> F   (arr U.! i))))
    ArrayPayloadDouble arr -> ArrayPayloadDouble (fromL (map unD  $ fn len (\i -> D   (arr U.! i))))
    ArrayPayloadChar   arr -> ArrayPayloadChar   (fromL (map unC  $ fn len (\i -> C   (arr U.! i))))
    ArrayPayloadBool   arr -> ArrayPayloadBool   (fromL (map fromBool$ fn len (\i -> toBool (arr U.! i))))
  where 
   fromL l = U.listArray (0,length l - 1) l
   unI   (I x) = x
   unI8  (I8 x) = x
   unI16 (I16 x) = x
   unI32 (I32 x) = x
   unI64 (I64 x) = x
   unW   (W x) = x
   unW8  (W8 x) = x
   unW16 (W16 x) = x
   unW32 (W32 x) = x
   unW64 (W64 x) = x
   unF (F x) = x
   unD (D x) = x
   unC (C x) = x
   unB (B x) = x
   toBool 0 = B False
   toBool _ = B True
   fromBool (B False) = 0
   fromBool (B True)  = 1


tracePrint s x = trace (s++show x) x