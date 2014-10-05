{-# LANGUAGE DeriveGeneric, CPP #-}
{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
-- TEMP: for UArray Read instance:
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances #-}

-- | This module defines the abstract syntax datatypes produced by the
--   simplified Accelerate backend-kit.  These datatypes are the
--   /starting point/ for any subsequent code generation performed by
--   a concrete backend.

module Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
   ( 
     -- * The types making up Accelerate ASTs:
     Prog(..), ProgBind(..), ProgResults(..),
     AExp(..), -- AFun(..), 
     Exp(..), TrivialExp(..), Fun1(Lam1), Fun2(..),
     Type(..), Const(..),
     Prim(..), NumPrim(..), IntPrim(..), FloatPrim(..), ScalarPrim(..), BoolPrim(..), OtherPrim(..),
     Boundary(..), Var, AVar,
          
     -- * Runtime Array data representation.
     AccArray(..), ArrayPayload(..), 

     -- * Shape representation:
     -- | Shapes are represented at runtime by tuples of integers.  For example:
     --    1D shape: (I 5)
     --    2D shape: Tup [I 2, I 3]
     --    3D shape: Tup [I 2, I 3, I 4]
     --   etc.
     
     -- * Slice representation
     SliceType, SliceComponent(..),
                
     -- * Helper routines and predicates:
     primArity, constToInteger, constToRational, constToNum, mkZeroConst,
     isIntType, isFloatType, isNumType, 
     isIntConst, isFloatConst, isNumConst, hasArrayType, flattenTy, flattenArrTy, countTyScalars,

     var, progToEnv, lookupProgBind, expFreeVars, expASTSize, 
     aexpFreeVars, aexpASTSize, progASTSize, 
     resultNames, resultShapeNames,

     showProgSummary,
     
     -- * Building and normalizing pieces of syntax
     normalizeEConst, mkTTuple, mkETuple,
     freshenExpNames, substExp, GensymM, genUnique, genUniqueWith, 
     
     -- * Type recovery and type checking:
     constToType, recoverExpType, topLevelExpType,
     typeByteSize, 
     accArrayToType, payloadToType
    )
 where

import           Control.DeepSeq (NFData(..))
import           Control.Monad.State.Strict (State, get, put)
import           Control.Applicative  ((<$>),(<*>))
import qualified Data.Array.IO     as IA
import qualified Data.Array.MArray as MA
import           Data.Array.Unboxed as U
import qualified Data.Array.Unsafe as Un
import           Data.Int
import qualified Data.Map          as M
import qualified Data.Set          as S
import qualified Data.List         as L
import           Data.Word
import           Foreign.C.Types 
import           Text.PrettyPrint.HughesPJ (text)
import           System.IO.Unsafe  (unsafePerformIO)
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)

import           Foreign.Storable (sizeOf)
-- import           System.Environment(getEnvironment)

--------------------------------------------------------------------------------
-- Prelude: Pick a simple representation of variables (interned symbols)
--------------------------------------------------------------------------------
-- Several modules offer this, with varying problems:
----------------------------
#define USE_STRING_VARIABLES
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
-- NOTE - this package would seem to be UNSAFE because the Symbol type
-- constructor is exported.
import Data.Symbol
var = intern
type Var = Symbol 
instance Read Symbol where 
  
#elif defined(USE_BYTESTRING_VARIABLES)

-- FINISHME

#elif defined(USE_STRING_VARIABLES)
var = Var 
newtype Var = Var String
  deriving (Eq, Ord)
instance Show Var where
  show (Var s) = s
instance Read Var where
  readsPrec i s = map (\ (a,b) -> (Var a,b)) (readsPrec i s)
instance NFData Var where
  rnf (Var s) = rnf s
#else
#error "Need to define some symbol representation for SimpleAcc.hs"
#endif
  
var :: String -> Var

-- | Array level variables.  Perhaps newtype this in the future.
type AVar = Var

--------------------------------------------------------------------------------
-- Complete Accelerate Programs
--------------------------------------------------------------------------------

-- | A complete program consists of a set of top-level array
--   bindings (with interdependencies), followed by a list
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
--   Note also that because there is no recursion, dependencies form a DAG.
--
--   Finally, each top-level binding is /decorated/ by a value of
--   indeterminite type (hence the type parameter).
data Prog decor = Prog { 
  progBinds   :: [ProgBind decor],
  progResults :: ProgResults,
  progType    :: Type,  -- Final, pre-flattened type, can be an array-tuple.
  uniqueCounter :: Int,  -- Counter for unique variable suffix generation

  -- | A cache for efficiency only.  This should contain bindings for a superset of
  -- all top-level variables bound by progBinds.  Most passes don't change this, so
  -- caching it here avoids rebuilding the `Map` many times.
  typeEnv :: M.Map Var Type
} deriving (Read,Show,Eq,Generic, Ord)

-- | The details of the what constitutes the final results changes
--  over the course of the compiler.  In general, results can be
--  tuples-of-arrays-of-tuples.  Also, the shape of the output
--  array(s) is an implicit output of the program.
data ProgResults = WithoutShapes [AVar]
                 | WithShapes [(AVar,Var)] -- ^ Later in the compiler.
                 | WithShapesUnzipped [(AVar,[Var])] 
                   -- ^ Even later, the shapes themselves have been unzipped.
  deriving (Read,Show,Eq,Generic, Ord)

-- | Report the names of the final result bindings from a program.  (Irrespective of
-- what other decorating information is attached.)
resultNames :: ProgResults -> [AVar]
resultNames (WithoutShapes ls)      = ls
resultNames (WithShapes ls)         = L.map fst ls  
resultNames (WithShapesUnzipped ls) = L.map fst ls  

-- | Returns a list with all shape names (may contain duplicates).
resultShapeNames :: ProgResults -> [Var]
resultShapeNames (WithoutShapes _ls)     = []
resultShapeNames (WithShapes ls)         = L.map snd ls  
resultShapeNames (WithShapesUnzipped ls) = concatMap snd ls  

-- | Print the binding structure and metadata of a program as a
-- multi-line string, without the contents of each array operation.
showProgSummary :: Show a => Prog a -> String
showProgSummary prg@Prog{progBinds,progResults,progType} = unlines $ 
  [ "Program Summary {"
  , "  AST Size: "++show (progASTSize prg)++", "++show (length progBinds)++" bindings"
  , "  Result type: "++show progType
  , "  Output variables: "++show progResults
  , "  Structure: " ] ++ structureLines ++ 
  [ "  Types and metadata: " ] ++ typeLines ++
  [ "}" ] 
 where 
  structureLines = map (("    "++) . summarizeBind) progBinds
  typeLines      = map (("    "++) . typeBind)      progBinds

  summarizeBind :: ProgBind a -> String
  summarizeBind (ProgBind v t _ (Left ex)) = 
    "scalar "++show v++
     (shorter (" = "++show ex)
              (", defined using "++show (S.toList (expFreeVars ex))))

  summarizeBind (ProgBind v t _ (Right ae)) = 
     "array "++show v++" = "++aexpOpName ae++
       (", defined using "++show (S.toList (aexpFreeVars ae)))
       -- case ae of 

  -- TODO: Align the three columns of this table:
  typeBind (ProgBind v t dec _) = show v++" :: "++show t++", "++ show dec

  shorter ls1 ls2 | length ls2 < length ls1 = ls2
                  | otherwise               = ls1            

-- | A top-level binding.  Binds a unique variable name to either an
--   array or scalar expression.
-- 
--   The `Type` corresponds to the type of the value on the
--   right-hand-side of the binding.  In addition, arbitrary metadata
--   is associated with the binding, hence the type parameter `decor`.
-- type ProgBind decor = (Var, Type, decor, Either Exp AExp)
data ProgBind decor = ProgBind Var Type decor (Either Exp AExp)
    deriving (Read,Show,Eq,Generic, Ord)
-- OR.....             
-- data ProgBind decor = ProgBind {
--     pbVar   :: Var,
--     pbType  :: Type,
--     pbDecor :: decor,
--     pbRHS   :: (Either Exp AExp)
--     } deriving (Read,Show,Eq,Generic)

instance Functor ProgBind where
  fmap fn (ProgBind v t dec rhs) = ProgBind v t (fn dec) rhs

-- TODO: invariant checker
-- checkValidProg

instance Functor Prog where
  fmap fn prog = prog{ progBinds= fmap (fmap fn) (progBinds prog) }
  
-- | O(N): look up a specific binding in a list of bindings.
--
-- In most cases you will want to create a Data.Map rather than using
-- this function so as to avoid quadratic complexity.
lookupProgBind :: Var -> [ProgBind a] -> Maybe (ProgBind a)
lookupProgBind _ [] = Nothing
lookupProgBind v (pb@(ProgBind v2 _ _ _) : rst) 
  | v == v2   = Just pb
  | otherwise = lookupProgBind v rst

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
    Vr Var                           -- ^ Array variable bound by a Let.
  | Unit Exp                         -- ^ Turn an element into a singleton array
  | Cond Exp Var Var                 -- ^ Array-level if statements
  | Use       AccArray               -- ^ A real live ARRAY goes here!
  | Generate  Exp (Fun1 Exp)         -- ^ Generate an array by applying a function to every index in shape
--  | AWhile  (Fun1 [ProgBind ()]) (Fun1 [ProgBind ()]) Var
  | Replicate SliceType Exp Var      -- ^ Replicate array across one or more dimensions.  
                                     --     Exp must return a shape value matching up with the to the SliceType.
  | Index     SliceType Var Exp      -- ^ Generalized indexing that can project a slice from an array.
                                     --     Var names the array.
                                     --     Exp must return a shape value matching up with the to the SliceType.
  | Map      (Fun1 Exp) Var          -- ^ Map Function Array
  | ZipWith  (Fun2 Exp) Var Var      -- ^ ZipWith Function Array1 Array2
  | Fold     (Fun2 Exp) Exp Var      -- ^ Fold Function Default Array
  | Fold1    (Fun2 Exp)     Var      -- ^ Fold1 Function Array
  | FoldSeg  (Fun2 Exp) Exp Var Var  -- ^ FoldSeg Function Default InArray SegmentDescriptor
  | Fold1Seg (Fun2 Exp)     Var Var  -- ^ FoldSeg Function         InArray SegmentDescriptor
  | Scanl    (Fun2 Exp) Exp Var      -- ^ Scanl  Function InitialValue LinearArray
  | Scanl'   (Fun2 Exp) Exp Var      -- ^ Scanl' Function InitialValue LinearArray
  | Scanl1   (Fun2 Exp)     Var      -- ^ Scanl  Function              LinearArray
  | Scanr    (Fun2 Exp) Exp Var      -- ^ Scanr  Function InitialValue LinearArray
  | Scanr'   (Fun2 Exp) Exp Var      -- ^ Scanr' Function InitialValue LinearArray
  | Scanr1   (Fun2 Exp)     Var      -- ^ Scanr  Function              LinearArray
  | Permute  (Fun2 Exp) Var (Fun1 Exp) Var -- ^ Permute CombineFun DefaultArr PermFun SourceArray
  | Backpermute Exp (Fun1 Exp) Var   -- ^ Backpermute ResultDimension   PermFun SourceArrayu
  | Reshape     Exp      Var         -- ^ Reshape Shape Array
  | Stencil  (Fun1 Exp) Boundary Var
  | Stencil2 (Fun2 Exp) Boundary Var Boundary Var -- ^ Two source arrays/boundaries
 deriving (Read,Show,Eq,Ord,Generic)


-- | Boundary condition specification for stencil operations.
data Boundary = Clamp               -- ^ clamp coordinates to the extent of the array
              | Mirror              -- ^ mirror coordinates beyond the array extent
              | Wrap                -- ^ wrap coordinates around on each dimension
              | Constant Const      -- ^ use a constant value for outlying coordinates 
 deriving (Read,Show,Eq,Ord,Generic)
          
          
--------------------------------------------------------------------------------
-- Accelerate Scalar Expressions and Functions
--------------------------------------------------------------------------------

-- | Functions, arity 1
data Fun1 a = Lam1 (Var,Type) a
 deriving (Read,Show,Eq,Ord,Generic)

-- | Functions, arity 2
data Fun2 a = Lam2 (Var,Type) (Var,Type) a
 deriving (Read,Show,Eq,Ord,Generic)

-- | Scalar expressions
data Exp = 
    EConst Const              -- ^ Constant.        
  | EVr Var                   -- ^ Variable bound by a Let.
  | ELet (Var,Type,Exp) Exp   -- ^ @ELet var type rhs body@,
                              --   used for common subexpression elimination
  | EPrimApp Type Prim [Exp]  -- ^ /Any/ primitive scalar function, including type of return value.
  | ECond Exp Exp Exp         -- ^ Conditional expression (non-strict in 2nd and 3rd argument).
  | EWhile (Fun1 Exp) (Fun1 Exp) Exp -- ^ A Scalar while loop
  | EIndexScalar Var Exp      -- ^ Project a single scalar from an array [variable].
  | EShape Var                -- ^ Get the shape of an Array [variable].
  | EShapeSize Exp            -- ^ Number of elements of a shape
  | EIndex [Exp]              -- ^ An index into a multi-dimensional array.
  | ETuple [Exp]              -- ^ Build a tuple.  They are store in REVERSE of textual order in the IR.
  | ETupProject               
    { indexFromRight :: Int,  -- ^ where to start the slice
      projlen        :: Int,  -- ^ how many scalars to extract
      tupexpr        :: Exp   -- ^ tuple value to extract from
    } -- ^ Project a consecutive series of fields from a tuple.
      -- This is an odd one because projlen is counted in terms of LEAVES of the tuple,
      -- if it is a nested tuple.  But the effect is always to 
 deriving (Read,Show,Eq,Ord,Generic)

-- | Trivial expressions.
--   It happens that the only trivial constants we need are of type TInt.
data TrivialExp = TrivConst Int | TrivVarref Var
 deriving (Read,Show,Eq,Ord,Generic)

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
 deriving (Read,Show,Eq,Ord,Generic)


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
data IntPrim = Quot | Rem |
               IDiv |  -- Integral division with truncation towards negative infinity.  I.e. 'div'
               Mod  | 
               BAnd | BOr | BXor | BNot | BShiftL | BShiftR | BRotateL | BRotateR
  deriving (Read,Show,Eq,Ord,Generic)

-- | Primitive floating point-only operations.
data FloatPrim = 
      -- Unary:
      Recip | Sin | Cos | Tan | Asin | Acos | Atan | Asinh | Acosh | Atanh | ExpFloating | Sqrt | Log |
      -- Unary but with different input and output types:
      Truncate | Round | Floor | Ceiling | 
      -- Binary:                  
      FDiv | FPow | LogBase | Atan2 
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
primArity p = case M.lookup p mp of
                Nothing -> error$"SimpleAcc.hs/primArity: prim was missing from table: "++show p
                Just x  -> x
 where 
  mp = M.fromList $ 
   zip binaries (repeat 2) ++
   zip unaries  (repeat 1)
  binaries = 
    [BP And, BP Or] ++
    [NP Add, NP Sub, NP Mul, IP BNot] ++
--    [ BAnd , BOr | BXor | BNot | BShiftL | BShiftR | BRotateL | BRotateR
    map IP [Quot, Rem, IDiv, Mod, BShiftL, BShiftR, BRotateL, BRotateR, 
            BOr, BXor, BAnd ] ++
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
 deriving (Read,Show,Eq,Generic,Ord)

type Dims = Int


-- | Slices of arrays.  These have a length matching the dimensionality of the slice.
-- The SliceType is only part of the story; it says what to do with each dimension
-- but not how BIG that dimension is.  Slicing-related operations also take a runtime
-- value specifying the sizes, which will contain a list of the same length as the
-- SliceType list.  The rule for these is that fixed dimensions must have a Int size,
-- and "All" dimensions don't require extra information, so they will match up with a
-- unit () value.
-- 
-- The resulting lists read right-to-left, in the OPPOSITE
-- order that one would write `(Z :. 3 :. 4 :. All)` in the source code;
-- i.e. that particular example would translate to `[All, Fixed, Fixed]`.
--
-- The result is that the "fastest varying" dimension is on the head of the list in
-- this representation.
-- 
type SliceType      = [SliceComponent]
data SliceComponent = Fixed | All 
  deriving (Eq,Show,Read,Ord,Generic)

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
--   contained in a "Data.Array.Accelerate.Array".  Going with the
--   theme of "SimpleAcc", the idea is to provide access in a form
--   that doesn't require complex types.  However, while simple in
--   that respect, this representation is also a pain to work with
--   because `ArrayPayload` is a large sum type.
-- 
--   Arrays of tuples are still "unzipped" in this representation
--   (i.e. represented as tuples of arrays).  The dimensions are
--   represented as a simple list of integers.  For example, [2,3,4]
--   would be dimensions for a three dimensional array.
-- 
--   Invariant: all payload arrays should be the same length, and:
-- 
--   > sum (arrDim a) == length (arrPayloads a !! i)
--
--   The array dimensions are stored from the "inner" to the "outer" dimension.
--   That is, if you do a fold, the first element of the list is the dimension
--   that gets squished away.
data AccArray = AccArray { arrDim :: [Int], arrPayloads :: [ArrayPayload] }
 deriving (Eq, Ord)

instance Show AccArray where
  show (AccArray shape payloads) =
        "AccArray "++show shape++
        (L.concat$ L.map  ((" "++) . doPayld) payloads)
   where
     doPayld p = 
       case p of 
         ArrayPayloadInt    arr -> show$ U.elems arr
         ArrayPayloadInt8   arr -> show$ U.elems arr
         ArrayPayloadInt16  arr -> show$ U.elems arr
         ArrayPayloadInt32  arr -> show$ U.elems arr
         ArrayPayloadInt64  arr -> show$ U.elems arr
         ArrayPayloadWord   arr -> show$ U.elems arr
         ArrayPayloadWord8  arr -> show$ U.elems arr
         ArrayPayloadWord16 arr -> show$ U.elems arr
         ArrayPayloadWord32 arr -> show$ U.elems arr
         ArrayPayloadWord64 arr -> show$ U.elems arr
         ArrayPayloadFloat  arr -> show$ U.elems arr
         ArrayPayloadDouble arr -> show$ U.elems arr
         ArrayPayloadChar   arr -> show$ U.elems arr
         ArrayPayloadBool   arr -> show$ U.elems arr
         ArrayPayloadUnit   len -> show$ replicate len ()

instance Read AccArray where
--  read str = error "FIXME: Read instance for AccArray is unfinished."

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
  | ArrayPayloadUnit   Int -- Dummy placeholder value, length only.
--  
-- TODO -- Add C-types.  But as of this date [2012.05.21], Accelerate
-- support for these types is incomplete, so we omit them here as well.
--   
-- TODO: UArray doesn't offer cast like IOArray.  It would be nice
-- to make all arrays canonicalized to a data buffer of Word8's:
 deriving (Show, Read, Eq, Ord)
  
-- | This is our Haskell representation of raw, contiguous data (arrays).
-- It is subject to change in the future depending on what internal
-- representation the Accelerate front-end uses.
type RawData e = UArray Int e

-- This will only report a FLAT tuple structure.  It does not keep additional type
-- information.
accArrayToType :: AccArray -> Type
accArrayToType (AccArray ls payls) =
  TArray (length ls) (mkTTuple (L.map payloadToType payls))

payloadToType :: ArrayPayload -> Type
payloadToType p =  
  case p of 
    ArrayPayloadInt    arr -> TInt
    ArrayPayloadInt8   arr -> TInt8
    ArrayPayloadInt16  arr -> TInt16
    ArrayPayloadInt32  arr -> TInt32
    ArrayPayloadInt64  arr -> TInt64
    ArrayPayloadWord   arr -> TWord
    ArrayPayloadWord8  arr -> TWord8
    ArrayPayloadWord16 arr -> TWord16
    ArrayPayloadWord32 arr -> TWord32
    ArrayPayloadWord64 arr -> TWord64
    ArrayPayloadFloat  arr -> TFloat
    ArrayPayloadDouble arr -> TDouble
    ArrayPayloadChar   arr -> TChar
    ArrayPayloadBool   arr -> TBool
    ArrayPayloadUnit   _   -> TTuple []

--------------------------------------------------------------------------------
-- Convenience functions for dealing with large sum types.
--------------------------------------------------------------------------------

-- | How many bytes will be used up by a type once emitted to C.
typeByteSize :: Type -> Int
typeByteSize ty =
  case ty of {
    TInt8 ->1;    TInt16  ->2;  TInt32  ->4;  TInt64 ->8;
    TWord8 ->1;   TWord16  ->2; TWord32  ->4; TWord64 ->8;
    TInt    -> sizeOf(err::Int);
--    TInt    -> 4;
    TWord   -> sizeOf(err::Word);    
    TCShort -> sizeOf(err::CShort);
    TCInt   -> sizeOf(err::CInt);
    TCLong  -> sizeOf(err::CLong);
    TCLLong -> sizeOf(err::CLLong);
    TCUShort ->sizeOf(err::CUShort);
    TCUInt   ->sizeOf(err::CUInt);
    TCULong  ->sizeOf(err::CULong);
    TCULLong ->sizeOf(err::CULLong);
    TCChar -> 1; TCSChar -> 1; TCUChar -> 1; -- C character types.
    TFloat  -> 4; TDouble  -> 8;
    TCFloat -> 4; TCDouble -> 8;
    TBool -> 1;   TChar -> 1; -- sizeOf(err::Char)
    TTuple ls -> sum$ map typeByteSize ls;
    TArray _ _ -> error "typeByteSize: cannot know the size of array from its type"
  }
 where
   err = error "typeByteSize: this should never be used"

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

-- | Does the type contain TArray?  I.e. is it either an array or a tuple of arrays?
hasArrayType :: Type -> Bool
hasArrayType (TArray _ _) = True
hasArrayType (TTuple ls) = any hasArrayType ls
hasArrayType _ = False

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
constToInteger :: Const -> Integer
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

-- | Convert any const satisfying `isNumConst` into a Haskell
--   `Double` value.  
-- constToDouble :: Const -> Double
-- constToDouble c = 
--   case c of 
--     c | isIntConst c -> fromInteger (constToInteger c)
--     D  f -> f
--     CD f -> fromRational $ toRational f
--     F  f -> fromRational $ toRational f
--     CF f -> fromRational $ toRational f
--     C    _  -> error "constToDouble: cannot convert TChar Const to Double"
--     B    _  -> error "constToDouble: cannot convert TBool Const to Double"
--     Tup  _  -> error "constToDouble: cannot convert tuple Const to Double"


-- TODO: we could go this route in the future:
-- instance Num  Const where 
-- instance Real Const where 
-- instance Ord  Const where 

-- -- For convenience we make it possible to call Haskell functions
-- -- directly on "Consts".  Be warned that these are PARTIAL functions,
-- -- some Consts and combinations of Consts certainly lead to errors.
-- instance Integral Const where 
--   toInteger x = 

-- | Unwrap a SimpleAcc `Const` (satisfying isIntConst) into a raw
--   Haskell number.  Note that this function may perform a size
--   conversion IF the type of the Const does not match the destination
--   Haskell type.
constToNum :: Num a => Const -> a 
constToNum c = 
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
    CULL n  -> fromIntegral n
    CC   n  -> fromIntegral n
    CUC  n  -> fromIntegral n
    CSC  n  -> fromIntegral n
    F    _  -> error "constToNum: cannot convert TFloat Const to a Num"
    CF   _  -> error "constToNum: cannot convert TCFloat Const to a Num"
    D    _  -> error "constToNum: cannot convert TDouble Const to a Num"
    CD   _  -> error "constToNum: cannot convert TCDouble Const to a Num"
    C    _  -> error "constToNum: cannot convert TChar Const to a Num"
    B    _  -> error "constToNum: cannot convert TBool Const to a Num"
    Tup  _  -> error "constToNum: cannot convert tuple Const to a Num"


mkZeroConst :: Type -> Const
mkZeroConst ty = 
  case ty of {
    TInt   ->I 0;  TInt8  -> I8 0;   TInt16  -> I16 0;  TInt32 -> I32 0; TInt64  -> I64 0; 
    TWord  ->W 0;  TWord8 -> W8 0;   TWord16 -> W16 0; TWord32 -> W32 0; TWord64 -> W64 0; 
    TCShort -> CS 0; TCInt -> CI 0;  TCLong  -> CL 0;  TCLLong -> CLL 0; 
    TCUShort -> CUS 0;  TCUInt -> CUI 0;  TCULong -> CUL 0;  TCULLong -> CULL 0;
    TCChar -> CC 0; TCSChar -> CSC 0; TCUChar -> CUC 0; -- C character types.
    _ -> error$ "mkZeroConst: cannot make a zero Const of this type: "++show ty
  }


-- | Unwrap a SimpleAcc `Const` (satisfying isNumConst) into a raw
--   Haskell Rational.
constToRational :: Const -> Rational 
constToRational c = 
  case c of 
    I   n -> toRational n
    I8  n -> toRational n
    I16 n -> toRational n
    I32 n -> toRational n
    I64 n -> toRational n
    W   n -> toRational n
    W8  n -> toRational n
    W16 n -> toRational n
    W32 n -> toRational n
    W64 n -> toRational n
    CS  n -> toRational n
    CI  n -> toRational n
    CL  n -> toRational n
    CLL n -> toRational n
    CUS n -> toRational n
    CUI n -> toRational n
    CUL n -> toRational n
    CULL n  -> toRational n
    CC   n  -> toRational n
    CUC  n  -> toRational n
    CSC  n  -> toRational n
    F    n  -> toRational n
    CF   n  -> toRational n
    D    n  -> toRational n
    CD   n  -> toRational n
    C    _  -> error "fromConst: cannot convert TChar Const to a Num"
    B    _  -> error "fromConst: cannot convert TBool Const to a Num"
    Tup  _  -> error "fromConst: cannot convert tuple Const to a Num"


----------------------------------------------------------------------------------------------------
-- Type checking:
----------------------------------------------------------------------------------------------------

-- | What is the type of a `Const`?
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

-- | Recover the type of a /top-level/ `Exp` occuring within a `Prog`.
-- The important distinction here is that the `Exp` may not have free
-- variables other than those bound at top-level (i.e. it may not be
-- inside a `ELet`).
--
topLevelExpType :: Prog a -> Exp -> Type
topLevelExpType pr exp = recoverExpType (progToEnv pr) exp 

-- | For creating an initial environment in which to use `recoverExpType`
progToEnv :: Prog a -> M.Map Var Type
-- Note this is highly INEFFICIENT -- it creates a map from the list every time:
-- Caching this when its needed repeatedly would be good.
progToEnv p = M.fromList$ map (\(ProgBind v ty _ _) -> (v,ty)) (progBinds p)

-- | Recover the type of an expression, given an environment.  The
-- environment must include bindings for any free scalar AND array
-- variables.
recoverExpType :: M.Map Var Type -> Exp -> Type
recoverExpType env exp = 
      case exp of
        EVr  v                -> case M.lookup v env of 
                                  Nothing -> error$"toplevelExpType: unbound scalar variable: "++show v
                                  Just ty -> ty
        EConst c              -> constToType c
        ELet (vr,ty,_) bod    -> recoverExpType (M.insert vr ty env) bod
        ETuple [x]            -> error$"recoverExpType: invariant broken, one element ETuple containing: "++show x
        ETuple es             -> TTuple$  map (recoverExpType env) es
        ECond _e1 e2 _e3      -> recoverExpType env e2
        EWhile _f1 _f2 e3     -> recoverExpType env e3
        EPrimApp ty _ _       -> ty
        EShapeSize _ex        -> TInt
        -- Shapes are represented as Tuples of Ints.  But we need to know how long:
        EShape vr             -> let (dim,_) = arrayType vr in 
                                 mkTTuple$ take dim (repeat TInt)          
        EIndexScalar vr _ex   -> snd (arrayType vr)
        ETupProject indR len ex -> let TTuple ls = recoverExpType env ex in 
                                   mkTTuple$ reverse $ take len $ drop indR $ reverse ls
        -- Indices are represented as Tuples:
        EIndex es             -> mkTTuple $ map (recoverExpType env) es
 where 
   arrayType vr = 
     case M.lookup vr env of 
       Nothing -> error$"recoverExpType:: unbound array variable: "++show vr
       Just (TArray dim elt) -> (dim,elt)
       Just _ -> error$"recoverExpType: internal error, array var has non-array type"++show vr


-- | Flatten any outer layers of tupling from a type.
--   This will NOT go under `TArray`s.
flattenTy :: Type -> [Type]
-- flattenTy (TTuple [])  = [TTuple []]
flattenTy (TTuple ls)  = concatMap flattenTy ls
flattenTy         ty  = [ty]

-- | Recursively concatenate tuple types into a flat list.  If given an array type,
-- flatten inside the array type and return a list of array types.
-- flattenArrTy :: Type -> [Type]
-- flattenArrTy (TTuple ls)    = concatMap flattenArrTy ls
-- flattenArrTy (TArray d elt) = map (TArray d) (flattenArrTy elt)
-- flattenArrTy         ty     = [ty]


-- | Only accept Array types.  Recursively concatenate tuple types into a flat list,
-- and split the array into separate (unzipped) arrays.
flattenArrTy :: Type -> [Type]
flattenArrTy (TArray d elt) = map (TArray d) (loop elt)
  where
  loop (TTuple [])  = [TTuple []]
  loop (TTuple ls)  = concatMap loop ls
  loop oth          = [oth]
flattenArrTy ty = error$"flattenArrTy should only take an array type: "++show ty

-- | Count the number of values when the type is flattened.  This counts through BOTH
-- arrays and tuples, so a tuple-of-arrays-of-tuples will be handled.
countTyScalars :: Type -> Int
countTyScalars = loop1
 where
  -- loop1 (TArray _ elt) = loop1 elt
  -- loop1 (TTuple [])    = 1
  -- loop1 (TTuple ls)    = sum$ map loop1 ls
  -- loop1 _              = 1 

  loop1 (TArray _ elt) = loop2 elt
  loop1 (TTuple ls)    = sum$ map loop1 ls
  loop1 _              = 1 
  -- Inside an array we must count an array of units as a value:
  loop2 (TArray _ elt) = loop2 elt
  loop2 (TTuple [])    = 1
  loop2 (TTuple ls)    = sum$ map loop2 ls
  loop2 _              = 1 




----------------------------------------------------------------------------------------------------
-- End Type Checking 
----------------------------------------------------------------------------------------------------

-- | Helper function for constructing TTuples, which must be non-empty:
mkTTuple :: [Type] -> Type
mkTTuple [ty] = ty
mkTTuple ls = TTuple ls

-- | For expressions as well as types, we ensure we do-not create an empty tuple.
--   (In the future it may be good to use a non-empty-list type explicitly.)
mkETuple :: [Exp] -> Exp
mkETuple [e] = e
mkETuple ls = ETuple ls

-- | Normalize an expression containing a constant.  This eliminates
-- redundant encodings of tuples.  In particular, it lifts `Tup`
-- constants out to `ETuple` expressions and it makes sure there are
-- no unary-tuples.
normalizeEConst :: Exp -> Exp
normalizeEConst e =
  case e of 
    EConst (Tup ls) -> normalizeEConst$ ETuple$ map EConst ls
    ETuple [x]      -> normalizeEConst x
    ETuple ls       -> ETuple$ map normalizeEConst ls
    -- FIXME: We need to phase out EIndex entirely.  They are just represented as tuples:
    EIndex ls       -> ETuple ls
    other           -> other

-- | Retrieve the set of variables that occur free in an `Exp`.
expFreeVars :: Exp -> S.Set Var
expFreeVars ex =
   let f                          = expFreeVars 
       fs                         = S.unions . map expFreeVars
       fn1 (Lam1 (v,_t) e)        = S.delete v $ f e
       fn2 (Lam2 (v1,_t1) (v2,_t2) e) = S.delete v1 $ S.delete v2 $ f e
   in
   case ex of
    EShape avr          -> S.singleton avr -- NOTE! THIS WILL CHANGE.
    EConst _            -> S.empty
    EVr vr              -> S.singleton vr  
    ECond e1 e2 e3      -> S.union (f e1)  $ S.union (f e2) (f e3)
    EWhile f1 f2 e3     -> S.union (fn1 f1) $ S.union (fn1 f2) (f e3)
    ELet (v,_,rhs) bod  -> S.union (f rhs) $ S.delete v $ f bod
    EIndexScalar avr ex -> S.insert avr $ f ex
    EShapeSize ex       -> f ex 
    ETupProject _ _ ex  -> f ex 
    ETuple els          -> fs els    
    EPrimApp _ _ els    -> fs els     
    EIndex els          -> fs els 

-- | Retrieve the set of variables that occur free in an `AExp`, including both
-- scalar and array variables.
aexpFreeVars :: AExp -> S.Set Var
aexpFreeVars ae =
  let g = expFreeVars
      fn1 (Lam1 (v,_t) e)          = S.delete v $ g e
      fn2 (Lam2 (v1,_t) (v2,_u) e) = S.delete v1 $ S.delete v2 $ g e
  in
  case ae of
    Vr v             -> S.singleton v
    Unit e           -> g e
    Cond e v1 v2     -> S.insert v1 $ S.insert v2 $ g e 
    Use     _        -> S.empty
    Generate  e f1   -> g e `S.union` fn1 f1
    Replicate _ e v  -> S.insert v $ g e 
    Index    _ v e   -> S.insert v $ g e 
    Map      f v     -> S.insert v $ fn1 f
    ZipWith  f v1 v2 -> S.insert v1 $ S.insert v2 $ fn2 f
    Fold     f e v   -> S.insert v $ S.union (g e) $ fn2 f
    Fold1    f   v   -> S.insert v $ fn2 f
    FoldSeg  f e v1 v2 -> S.unions [ fn2 f, g e, S.singleton v1, S.singleton v2 ]
    Fold1Seg f   v1 v2 -> S.insert v1 $ S.insert v2 $ fn2 f
    Scanl    f e v     -> S.insert v $ fn2 f `S.union` g e
    Scanl'   f e v     -> S.insert v $ fn2 f `S.union` g e
    Scanl1   f   v     -> S.insert v $ fn2 f 
    Scanr    f e v     -> S.insert v $ fn2 f `S.union` g e
    Scanr'   f e v     -> S.insert v $ fn2 f `S.union` g e
    Scanr1   f   v     -> S.insert v $ fn2 f 
    Permute  f v1 f1 v2 -> S.insert v1 $ S.insert v2 $ fn2 f `S.union` fn1 f1
    Backpermute e f1 v  -> S.insert v $ fn1 f1 `S.union` g e
    Reshape     e    v  -> S.insert v $ g e
    Stencil  f1 _bound v -> S.insert v $ fn1 f1
    Stencil2 f2 _b1 v1 _b2 v2 -> S.insert v1 $ S.insert v2 $ fn2 f2


aexpOpName :: AExp -> String
aexpOpName ae =
  case ae of
    Vr v             -> "Vr"
    Unit e           -> "Unit"
    Cond e v1 v2     -> "Cond"
    Use     _        -> "Use"
    Generate  e f1   -> "Generate"
    Replicate _ e v  -> "Replicate"
    Index    _ v e   -> "Index"
    Map      f v     -> "Map"
    ZipWith  f v1 v2 -> "ZipWith"
    Fold     f e v   -> "Fold"
    Fold1    f   v   -> "Fold1"
    FoldSeg  f e v1 v2 -> "FoldSeg"
    Fold1Seg f   v1 v2 -> "Fold1Seg"
    Scanl    f e v     -> "Scanl"
    Scanl'   f e v     -> "Scanl'"
    Scanl1   f   v     -> "Scanl1"
    Scanr    f e v     -> "Scanr"
    Scanr'   f e v     -> "Scanr'"
    Scanr1   f   v     -> "Scanr1"
    Permute  f v1 f1 v2 -> "Permute"
    Backpermute e f1 v  -> "Backpermute"
    Reshape     e    v  -> "Reshape"
    Stencil  f1 _bound v -> "Stencil"
    Stencil2 f2 _b1 v1 _b2 v2 -> "Stencil2"

-- | Alpha-rename all variables to fresh names.
freshenExpNames :: Exp -> GensymM Exp
freshenExpNames = lp M.empty
  where
    lp env ex =
     let f = lp env
         rfn1 (Lam1 (v,t) e) = do v' <- genUniqueWith (show v)
                                  e' <- lp (M.insert v v' env) e
                                  return (Lam1 (v',t) e')
     in
     case ex of
      ELet (v,ty,rhs) bod  -> do v' <- genUniqueWith (show v)
                                 rhs' <- f rhs
                                 bod' <- lp (M.insert v v' env) bod
                                 return (ELet (v',ty,rhs') bod')
      EVr vr              -> case M.lookup vr env of
                               Nothing -> return ex
                               Just v' -> return (EVr v')
       
      EShape _avr         -> return ex
      EConst _            -> return ex
      ECond e1 e2 e3      -> ECond <$> f e1 <*> f e2 <*> f e3
      EWhile f1 f2 e3     -> do f1 <- rfn1 f1
                                f2 <- rfn1 f2
                                e3 <- f e3
                                return (EWhile f1 f2 e3)
      EIndexScalar avr e  -> EIndexScalar avr <$> f e
      EShapeSize e        -> EShapeSize       <$> f e
      ETupProject i l e   -> ETupProject i l  <$> f e
      ETuple els          -> ETuple       <$> mapM f els
      EPrimApp t p els    -> EPrimApp t p <$> mapM f els
      EIndex els          -> EIndex       <$> mapM f els


-- | How many nodes are contained in an Exp?
expASTSize :: Exp -> Int
expASTSize ex0 =
   let f = expASTSize in
   case ex0 of
    EShape _avr         -> 1
    EConst _            -> 1 -- Could measure const size.
    EVr _               -> 1
    ECond a b c         -> 1 + f a + f b + f c
    EWhile f1 f2 c      -> 1 + fn1 f1 + fn1 f2 + f c
    ELet (_,_,rhs) bod  -> 1 + f rhs + f bod
    EIndexScalar _av ex -> 1 + f ex 
    EShapeSize ex       -> 1 + f ex
    ETupProject _ _ ex  -> 1 + f ex 
    ETuple els          -> 1 + sum (map f els)
    EPrimApp _ _ els    -> 1 + sum (map f els)
    EIndex els          -> 1 + sum (map f els)

fn1 :: Fun1 Exp -> Int
fn1 (Lam1 (_,t)   e)     = expASTSize e + typeSize t

fn2 :: Fun2 Exp -> Int
fn2 (Lam2 (_,t) (_,u) e) = expASTSize e + typeSize t + typeSize u

typeSize :: Type -> Int
typeSize _ = 0 -- TODO: probably should count types.


aexpASTSize :: AExp -> Int
aexpASTSize ae =
  let g = expASTSize
  in
  case ae of
    Vr v             -> 1 
    Unit e           -> 1 + g e
    Cond e  _ _      -> 1 + g e 
    Use     _        -> 1 -- Could add in array size here, but that should probably be reported separately.
    Generate  e f1   -> 1 + g e + fn1 f1         -- Generate an array by applying a function to every index in shape
    Replicate _ e _  -> 1 + g e 
    Index    _ _ e   -> 1 + g e 
    Map      f _     -> 1 + fn1 f
    ZipWith  f _ _   -> 1 + fn2 f
    Fold     f e _   -> 1 + fn2 f
    Fold1    f     _ -> 1 + fn2 f
    FoldSeg  f e _ _    -> 1 + fn2 f + g e
    Fold1Seg f     _ _  -> 1 + fn2 f 
    Scanl    f e _      -> 1 + fn2 f + g e
    Scanl'   f e _      -> 1 + fn2 f + g e
    Scanl1   f     _    -> 1 + fn2 f 
    Scanr    f e _      -> 1 + fn2 f + g e
    Scanr'   f e _      -> 1 + fn2 f + g e
    Scanr1   f     _    -> 1 + fn2 f 
    Permute  f _ f1 _   -> 1 + fn2 f + fn1 f1
    Backpermute e f1 _  -> 1 + fn1 f1 + g e
    Reshape     e    _  -> 1 + g e 
    Stencil  f1 _ _     -> 1 + fn1 f1
    Stencil2 f2 _ _ _ _ -> 1 + fn2 f2

-- | How big is the AST of a program.
progASTSize :: Prog a -> Int
progASTSize Prog{progBinds, progResults} =
    sum $ map pb progBinds
  where
    pb (ProgBind _ _ty _ (Right ae)) = aexpASTSize ae
    pb (ProgBind _ _ty _ (Left  ex)) = expASTSize  ex

-- | Substitute an expression for all occurrences of a variable in an open
-- expression.
substExp :: Var -> Exp -> Exp -> Exp
substExp old new target = loop target
 where
   rfn1 (Lam1 (v,t) e) = Lam1 (v,t) $ if v == old
                                      then e
                                      else loop e
   loop ex =
    case ex of
      ELet (v,ty,rhs) bod -> let rhs' = loop rhs in
                             ELet (v,ty,rhs') $ 
                               if v == old
                               then bod
                               else loop bod 
      EVr vr              -> if vr == old
                             then new
                             else ex       
      EShape _avr         -> ex
      EConst _            -> ex
      ECond e1 e2 e3      -> ECond (loop e1) (loop e2) (loop e3)
      EWhile f1 f2 e3     -> EWhile (rfn1 f1) (rfn1 f2) (loop e3)
      EIndexScalar avr e  -> EIndexScalar avr (loop e)
      EShapeSize e        -> EShapeSize  (loop e)
      ETupProject i l e   -> ETupProject i l (loop e)
      ETuple els          -> ETuple       (map loop els)
      EPrimApp t p els    -> EPrimApp t p (map loop els)
      EIndex els          -> EIndex       (map loop els)


-- Lifting these here from Helpers.hs to avoid import cycles:
------------------------------------------------------------
-- | A monad to use just for gensyms:
type GensymM = State Int 
-- | Generate a unique name
genUnique :: GensymM Var
genUnique = genUniqueWith "gensym_"
-- | Generate a unique name with user-provided "meaningful" prefix.
genUniqueWith :: String -> GensymM Var
genUniqueWith prefix =
  do cnt <- get
     put (cnt+1)
     return$ var$ prefix ++ show cnt
------------------------------------------------------------

--------------------------------------------------------------------------------
-- Boilerplate for generic pretty printing:

instance Out Type
instance Out a => Out (Prog a)
instance Out a => Out (ProgBind a)
instance Out ProgResults
-- instance Out Fun1
-- instance Out Fun2
instance Out (Fun1 Exp)
instance Out (Fun2 Exp)
instance Out Exp
instance Out TrivialExp
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

instance (Out k, Out v) => Out (M.Map k v) where
  docPrec n m = docPrec n $ M.toList m
  doc         = docPrec 0 
  
-- Why is this one not included in the array package?:
instance (Read elt, U.IArray UArray elt) => Read (U.UArray Int elt) where
    readsPrec p = readParen (p > 9)
           (\r -> [(U.array b as :: U.UArray Int elt, u) | 
                   ("array",s) <- lex r,
                   (b,t)       <- reads s,
                   (as :: [(Int,elt)],u) <- reads t ])


test :: UArray Int Int
test = read "array (1,5) [(1,200),(2,201),(3,202),(4,203),(5,204)]" :: U.UArray Int Int


-- More ugly boilerplate for NFData
----------------------------------------------------------------------------------------------------

instance NFData a => NFData (Prog a) where
  rnf (Prog {progBinds=pbs, progResults=pr, progType=pt } ) =
    case rnf pbs of
     () -> case rnf pr of
           () -> case rnf pt of
                 () -> ()
                 
instance NFData a => NFData (ProgBind a) where
  rnf (ProgBind v t d rhs) = 
    seq (rnf v) $ 
    seq (rnf t) $
    seq (rnf d) $
    seq (rnf rhs) ()

instance NFData Type where
  rnf ty = error "FINISH ME"

instance NFData Exp where
  rnf ex = error "FINISH ME"
  
instance NFData AExp where
  rnf ae = error "FINISH ME"

instance NFData ProgResults where
  rnf (WithShapes ls)    = rnf ls
  rnf (WithoutShapes ls) = rnf ls
  rnf (WithShapesUnzipped ls) = rnf ls  

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


