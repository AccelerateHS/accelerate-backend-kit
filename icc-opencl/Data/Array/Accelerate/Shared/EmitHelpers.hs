{-# LANGUAGE OverloadedStrings #-}

module Data.Array.Accelerate.Shared.EmitHelpers
       (
         -- * Some help with code-emission:
         emitCType, emitOpenCLType,
         builderName,

         -- * Miscellaneous helpers
         fragileZip, (#)
       )
       where


import Data.Array.Accelerate.Shared.EasyEmit as EE

import qualified Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc  as S
import Text.PrettyPrint.HughesPJ as PP
import Foreign.Storable (sizeOf)
import qualified Prelude as P
import Prelude (error, ($), (.), (++), show, return, Show, Maybe(..))
import Data.Int (Int)
import Data.Word (Word)
import Debug.Trace (trace)

import Control.Monad.State.Strict (State, get, put)
import Control.Applicative ((<$>),(<*>),pure,Applicative)


----------------------------------------------------------------------------------------------------
-- Emission:
----------------------------------------------------------------------------------------------------


-- | During final C/OpenCL emission, create a name for a function that
-- executes a specific array operator.  That is, if you know the name
-- of an array variable, this will tell you what function to call to
-- populate that array.
builderName :: Var -> P.String
builderName vr = "build_" P.++ P.show vr


-- | Convert a type to the equivalent C type.
emitCType :: Type -> Syntax
-- NOTE! In the future this will have to grow more complex to track dimension:
emitCType (TArray dim elt) = emitCType elt +++ str "*"
emitCType ty = toSyntax$ text$ 
  case ty of
    TInt   -> case sizeOf (0::Int) of
                4 -> "int32_t"
                8 -> "int64_t"
    TInt8  -> "int8_t"
    TInt16 -> "int16_t"
    TInt32 -> "int32_t"
    TInt64 -> "int64_t"
    TWord  -> case sizeOf (0::Word) of
                4 -> "uint32_t"
                8 -> "uint64_t"    
    TWord8  -> "uint8_t"
    TWord16 -> "uint16_t"
    TWord32 -> "uint32_t"
    TWord64 -> "uint64_t"
    TCShort  -> "short"
    TCInt  -> "int"
    TCLong  -> "long"
    TCLLong -> "long long"
    TCUShort -> "unsigned short"
    TCUInt -> "unsigned int"
    TCULong -> "unsigned long"
    TCULLong -> "unsigned long long"
    TCChar    -> "char"
    TCUChar   -> "unsigned char"
    TCSChar   -> "char"
    TFloat     -> "float"
    TCFloat    -> "float"
    TDouble     -> "double"
    TCDouble    -> "double"
    TChar       -> "char"
    TBool       -> "bool"
--    TTuple [] -> "void"
    TTuple [] -> "int" -- [2014.02.22] Putting in real arrays of unit
    TTuple _  -> error "emitCType: cannot handle tuples presently"

-- | Convert a type to the equivalent OpenCL type.  Note that unlike
-- plain C, OpenCL provides specific guarantees as to the size of
-- standard numeric types like "int".  Thus this function differs
-- significantly from its counterpart for plain C types.
emitOpenCLType :: Type -> Syntax
-- NOTE! In the future this will have to grow more complex to track dimension:
emitOpenCLType (TArray dim elt) = emitOpenCLType elt +++ "*"
emitOpenCLType ty = toSyntax$ text$ 
  case ty of
    -- This is the size of a HASKELL Int:
    TInt   -> case sizeOf(0::Int) of
                4 -> "int"
                8 -> "long" -- In GHC, unlike C, Ints are 64 bit on a 64 bit platform.
                oth -> error$"unexpected Int byte size: " P.++ P.show oth
    TWord   -> case sizeOf(0::Word) of
                4 -> "unsigned int"
                8 -> "unsigned long"
                oth -> error$ "unexpected Word byte size: " P.++ P.show oth
    TInt8  -> "char"
    TInt16 -> "short"
    TInt32 -> "int"
    TInt64 -> "long"    
    TWord8  -> "unsigned char"
    TWord16 -> "unsigned short"
    TWord32 -> "unsigned int"
    TWord64 -> "unsigned long"
    TCShort -> "short"
    TCInt   -> "int"
    TCLong  -> "int"
    TCLLong -> "long"
    TCUShort -> "unsigned short"
    TCUInt   -> "unsigned int"
    TCULong  -> "unsigned int"
    TCULLong -> "unsigned long"
    TCChar   -> "char"
    TCUChar  -> "unsigned char"
    TCSChar  -> "char"
    TFloat   -> "float"
    TCFloat  -> "float"
    TDouble  -> "double"
    TCDouble -> "double"
    TChar    -> "char"
    TBool    -> "bool"
    TTuple [] -> "void"
    TTuple _  -> error "emitOpenCLType: cannot handle tuples presently"
    TArray dim elt -> error "cannot happen"


str = toSyntax . text


-- | Do not allow the lists to be different lengths.
fragileZip :: (Show t1, Show t2) =>
              [t1] -> [t2] -> [(t1, t2)]
fragileZip a b = loop a b
  where
    loop [] []           = []
    loop (h1:t1) (h2:t2) = (h1,h2) : loop t1 t2
    loop _ _             = error$"JIT.hs/fragileZip: lists were not the same length: "++show a++" "++show b


-- | For debugging purposes we should really never use Data.Map.!  This is an
-- alternative with a better error message.
(#) :: (P.Ord a1, Show a, Show a1) => M.Map a1 a -> a1 -> a
mp # k = case M.lookup k mp of
          Nothing -> error$"Map.lookup: key "++show k++" is not in map:\n  "++show mp
          Just x  -> x
