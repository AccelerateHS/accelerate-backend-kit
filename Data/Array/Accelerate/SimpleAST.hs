{-# LANGUAGE DeriveGeneric, CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- TEMP: for UArray Read instance:
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances #-}

-- | This module defines the abstract syntax datatypes produced by the
--   simplified Accelerate backend-kit.  These datatypes are the
--   /starting point/ for any subsequent code generation performed by
--   a concrete backend.
module Data.Array.Accelerate.SimpleAST  
   ( 
     -- * The types making up Accelerate ASTs:
     Prog(..),
     AExp(..), -- AFun(..), 
     Exp(..), Fun1(..), Fun2(..),
     Type(..), Const(..),
     Prim(..), NumPrim(..), IntPrim(..), FloatPrim(..), ScalarPrim(..), BoolPrim(..), OtherPrim(..),
     Boundary(..),
     Var,
          
     -- * Runtime Array data representation.
     AccArray(..), ArrayPayload(..), 
     
     -- * Slice representation
     SliceType(..), SliceComponent(..),
           
     -- * Helper routines and predicates:
     var, primArity, constToInteger, fromConst, 
     isIntType, isFloatType, isNumType, 
     isIntConst, isFloatConst, isNumConst,
     constToType
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
-- Complete Accelerate Programs
--------------------------------------------------------------------------------

-- | A complete program consists of a set of top-level array
--   bindings (with mutual interdependencies), followed by a list
--   (tuple) of result arrays.
-- 
--   The top level bindings may bind either arrays or scalar
--   expressions.  (Scalars are used for conditionals and other
--   arguments to array operations.)  These bindings could be in two
--   separate lists, and there is no necessary order except as implied
--   by data dependencies.  However, for convenience we maintain the
--   invariant that the binding list is topologically sorted and can
--   thus be evaluated in order.
-- 
--   Note that because there is no recursion, dependencies form a DAG.
data Prog = Prog { 
  progBinds   :: [(Var,Type,Either Exp AExp)],
  progResults :: [Var],
  progType    :: Type -- Final, pre-flattened type, can be an array-tuple.
} deriving (Read,Show,Eq,Generic)


-- TODO: invariant checker
-- checkValidProg


--------------------------------------------------------------------------------
-- Accelerate Array-level Expressions
--------------------------------------------------------------------------------

-- | Array-level expressions.  
-- 
-- Many of these constructors contain the result type as the first
-- field.  Types on `Let`s are the only really important ones, but the
-- others can reduce headaches when consuming the AST for constructs
-- like Replicate that change the type.
data AExp = 
    Vr Var                           -- Array variable bound by a Let.
  | Unit Exp                         -- Turn an element into a singleton array
  | Let (Var,Type,AExp) AExp         -- Let Var Type RHS Body
                                     -- Let is used for common subexpression elimination
  | Cond Exp Var Var                 -- Array level if statements
  | Use       Type AccArray          -- A real live ARRAY goes here!
  | Generate  Type Exp (Fun1 Exp)    -- Generate Function Array, very similar to map
  | Replicate Type SliceType Exp Var -- Replicate array across one or more dimensions.
  | Index     SliceType Var Exp      -- Index a sub-array (slice).
                                     --   (Index sliceIndex Array SliceDims)
  | Map      (Fun1 Exp) Var          -- Map Function Array
  | ZipWith  (Fun2 Exp) Var Var      -- ZipWith Function Array1 Array2
  | Fold     (Fun2 Exp) Exp Var      -- Fold Function Default Array
  | Fold1    (Fun2 Exp)     Var      -- Fold1 Function Array
  | FoldSeg  (Fun2 Exp) Exp Var Var  -- FoldSeg Function Default InArray SegmentDescriptor
  | Fold1Seg (Fun2 Exp)     Var Var  -- FoldSeg Function         InArray SegmentDescriptor
  | Scanl    (Fun2 Exp) Exp Var      -- Scanl  Function InitialValue LinearArray
  | Scanl'   (Fun2 Exp) Exp Var      -- Scanl' Function InitialValue LinearArray
  | Scanl1   (Fun2 Exp)     Var      -- Scanl  Function              LinearArray
  | Scanr    (Fun2 Exp) Exp Var      -- Scanr  Function InitialValue LinearArray
  | Scanr'   (Fun2 Exp) Exp Var      -- Scanr' Function InitialValue LinearArray
  | Scanr1   (Fun2 Exp)     Var      -- Scanr  Function              LinearArray
  | Permute  (Fun2 Exp) Var (Fun1 Exp) Var -- Permute CombineFun DefaultArr PermFun SourceArray
  | Backpermute Exp (Fun1 Exp) Var   -- Backpermute ResultDimension   PermFun SourceArray
  | Reshape     Exp      Var         -- Reshape Shape Array
  | Stencil  (Fun1 Exp) Boundary Var
  | Stencil2 (Fun2 Exp) Boundary Var Boundary Var -- Two source arrays/boundaries
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

-- | Functions, arity 1
data Fun1 a = Lam1 (Var,Type) a
 deriving (Read,Show,Eq,Generic)

-- | Functions, arity 2
data Fun2 a = Lam2 (Var,Type) (Var,Type) a
 deriving (Read,Show,Eq,Generic)

-- | Scalar expressions
data Exp = 
    EConst Const              -- Constant.        
  | EVr Var                   -- Variable bound by a Let.
  | ELet (Var,Type,Exp) Exp   -- @ELet var type rhs body@,
                              -- used for common subexpression elimination
  | EPrimApp Type Prim [Exp]  -- *Any* primitive scalar function, including type of return value.
  | ECond Exp Exp Exp         -- Conditional expression (non-strict in 2nd and 3rd argument).
  | EIndexScalar Var Exp      -- Project a single scalar from an array [variable],
                              -- the array expression can not contain any free scalar variables.
  | EShape Var                -- Get the shape of an Array [variable].
  | EShapeSize Exp            -- Number of elements of a shape
  | EIndex [Exp]              -- An index into a multi-dimensional array.
  | ETuple [Exp]              -- Build a tuple.
  | ETupProject {             -- Project a consecutive series of fields from a tuple.
      indexFromRight :: Int , --  * where to start the slice
      len            :: Int , --  * how many scalars to extract
      tupexpr        :: Exp }
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
  
-- | This is our Haskell representation of raw, contiguous data (arrays).
-- It is subject to change in the future depending on what internal
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
isNumType :: Type -> Bool
isNumType ty = isIntType ty || isFloatType ty

-- | Is the scalar type integral?  This includes words as well as
-- signed ints as well as C types.
isIntType :: Type -> Bool
isIntType ty =
  case ty of {
    TInt  ->t;     TInt8 ->t;    TInt16  ->t;  TInt32  ->t;  TInt64 ->t; 
    TWord  ->t;    TWord8 ->t;   TWord16  ->t; TWord32  ->t; TWord64 ->t; 
    TCShort  ->t;  TCInt   ->t;  TCLong  ->t;  TCLLong ->t; 
    TCUShort ->t;  TCUInt  ->t;  TCULong ->t;  TCULLong ->t;
    TCChar -> t; TCSChar -> t; TCUChar -> t; -- C character types.
     _ -> False
  }
 where t = True

isFloatType :: Type -> Bool
isFloatType ty = 
  case ty of {
    TFloat  ->t; TDouble ->t; 
    TCFloat ->t; TCDouble ->t;
    _ -> False  
  }
 where t = True

-- | Is it a numeric constant representing an exact integer?  This
-- includes words as well as signed ints as well as C types.
isIntConst :: Const -> Bool
isIntConst c =
  case c of {
    I _ ->t;    I8 _ ->t;    I16 _  ->t;  I32 _  ->t;  I64 _ ->t; 
    W _ ->t;    W8 _ ->t;    W16 _  ->t;  W32 _  ->t;  W64 _ ->t;     
    CS _ ->t;  CI _ ->t;  CL _ ->t;  CLL _ ->t; 
    CUS _ ->t;  CUI _ ->t;  CUL _ ->t;  CULL _ ->t;
    CC _ -> t; CSC _ -> t; CUC _ -> t; -- C char types count as ints.
     _ -> False
  }
 where t = True

-- | Is the constant an inexact floating point number (of any precision)?
isFloatConst :: Const -> Bool
isFloatConst c = 
  case c of {
    F _ ->t;  D _ ->t; 
    CF _ ->t; CD _ ->t;
    _ -> False  
  }
 where t = True

-- | Is the constant numeric, rather than a tuple, boolean or
-- character.  Note that C characters are considered numeric.
isNumConst :: Const -> Bool
isNumConst cnst = isIntConst cnst || isFloatConst cnst


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
    CUS n -> toInteger n
    CUI n -> toInteger n
    CUL n -> toInteger n
    CULL n -> toInteger n
    CC   n  -> toInteger n
    CUC  n  -> toInteger n
    CSC  n  -> toInteger n
    F    _  -> error "constToInteger: cannot convert TFloat Const to Integer"
    CF   _  -> error "constToInteger: cannot convert TCFloat Const to Integer"
    D    _  -> error "constToInteger: cannot convert TDouble Const to Integer"
    CD   _  -> error "constToInteger: cannot convert TCDouble Const to Integer"
    C    _  -> error "constToInteger: cannot convert TChar Const to Integer"
    B    _  -> error "constToInteger: cannot convert TBool Const to Integer"
    Tup  _  -> error "constToInteger: cannot convert tuple Const to Integer"

-- TODO: we could go this route in the future:

-- instance Num  Const where 
-- instance Real Const where 
-- instance Ord  Const where 

-- -- For convenience we make it possible to call Haskell functions
-- -- directly on "Consts".  Be warned that these are PARTIAL functions,
-- -- some Consts and combinations of Consts certainly lead to errors.
-- instance Integral Const where 
--   toInteger x = 
  
fromConst :: Num a => Const -> a 
fromConst c = 
  case c of 
    I   n -> fromIntegral n
    I8  n -> fromIntegral n
    I16 n -> fromIntegral n
    I32 n -> fromIntegral n
    I64 n -> fromIntegral n
    W   n -> fromIntegral n
    W8  n -> fromIntegral n
    W16 n -> fromIntegral n
    W32 n -> fromIntegral n
    W64 n -> fromIntegral n
    CS  n -> fromIntegral n
    CI  n -> fromIntegral n
    CL  n -> fromIntegral n
    CLL n -> fromIntegral n
    CUS n -> fromIntegral n
    CUI n -> fromIntegral n
    CUL n -> fromIntegral n
    CULL n -> fromIntegral n
    CC   n  -> fromIntegral n
    CUC  n  -> fromIntegral n
    CSC  n  -> fromIntegral n
    F    _  -> error "fromConst: cannot convert TFloat Const to a Num"
    CF   _  -> error "fromConst: cannot convert TCFloat Const to a Num"
    D    _  -> error "fromConst: cannot convert TDouble Const to a Num"
    CD   _  -> error "fromConst: cannot convert TCDouble Const to a Num"
    C    _  -> error "fromConst: cannot convert TChar Const to a Num"
    B    _  -> error "fromConst: cannot convert TBool Const to a Num"
    Tup  _  -> error "fromConst: cannot convert tuple Const to a Num"
    
constToType :: Const -> Type
constToType c = 
  case c of {
    I _ ->TInt;       I8  _ ->TInt8;  I16 _  ->TInt16;  I32 _ ->TInt32;  I64 _ ->TInt64; 
    W _ ->TWord;      W8  _ ->TWord8; W16 _  ->TWord16; W32 _ ->TWord32; W64 _ ->TWord64;
    CS _ ->TCShort;   CI  _ ->TCInt;  CL  _  ->TCLong;  CLL _ ->TCLLong; 
    CUS _ ->TCUShort; CUI _ ->TCUInt; CUL _  ->TCULong; CULL _ ->TCULLong;
    CF _ -> TCFloat;  CD _ -> TCDouble; CC _ -> TCChar; CSC _ -> TCSChar; CUC _ -> TCUChar;
    F _ -> TFloat; D _ -> TDouble; C _ -> TChar; B _ -> TBool;
    Tup ls -> TTuple $ map constToType ls
  }


--------------------------------------------------------------------------------
-- Boilerplate for generic pretty printing:

instance Out Type
instance Out Prog
-- instance Out Fun1
-- instance Out Fun2
instance Out (Fun1 Exp)
instance Out (Fun2 Exp)
instance Out Exp
instance Out AExp
-- instance Out AFun
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
-- This just converts the non-pretty version:
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