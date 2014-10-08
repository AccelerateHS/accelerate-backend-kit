{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Utilities for working with the simplified representation of
--   Accelerate arrays on the Haskell heap.
-- 
--   These functions should mainly be used for constructing
--   interpreters and reference implementations.  Many of them are
--   unsuited for high-performance scenarios.
module Data.Array.Accelerate.BackendKit.SimpleArray
   ( 
          
     -- * Runtime Array data representation.
     AccArray(..), ArrayPayload(..),  -- Reexported from SimpleAST

     -- * Data invariant validation and recovery
     verifyAccArray, reglueArrayofTups,
     
     -- * Functions for operating on `AccArray`s
     mapArray,
     splitComponent, numComponents,
     indexArray,
     splitAccArray,

     -- * Functions for constructing `AccArray`s
     Data.Array.Accelerate.BackendKit.SimpleArray.replicate,      
     
     -- * Functions for operating on payloads (internal components of AccArrays)
     payloadToPtr, payloadFromPtr,
     payloadToList, payloadsFromList, payloadsFromList1,
     payloadLength, 
     mapPayload, indexPayload,
     
     applyToPayload, applyToPayload2, applyToPayload3,
     concatAccArrays
   )
   
where 

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendKit.Utils.Helpers (maybtrace)

import           Control.Applicative ((<$>))
import qualified Data.Array.IO     as IA
import qualified Data.Array.MArray as MA
import           Data.Array.Storable.Internals
import qualified Data.Array.Unsafe as Un
import           Data.Int
import           Data.List          as L
import qualified Data.Map          as M
import           Data.Maybe   (catMaybes)
import qualified Data.Primitive.ByteArray as BA
import           Data.Primitive.Types (Addr(Addr))
import           Data.Word
import           Debug.Trace
import           Foreign.C.Types
import           Foreign.ForeignPtr
import           Foreign.ForeignPtr.Unsafe
import           Foreign.Marshal.Array (copyArray)
import           Foreign.Storable      (Storable, sizeOf)
import           GHC.Prim         (byteArrayContents#, newPinnedByteArray#)
import           GHC.Ptr          (Ptr(Ptr), castPtr)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
-- import GHC.Prim           (newPinnedByteArray#, byteArrayContents#,
--                            unsafeFreezeByteArray#, Int#, (*#))
----------------------------------------------------------------------------------------------------
-- Helper functions for working with Array data living on the Haskell heap:
----------------------------------------------------------------------------------------------------

-- | How many elements are in the payload?  This handles the annoying
--   large case dispatch on element type.
payloadLength :: ArrayPayload -> Int
payloadLength payl =
  case payl of 
--    ArrayPayloadUnit       -> 0
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
    ArrayPayloadUnit   len -> len
 

-- | Dereference an element within a payload.  Payload is indexed in
-- the same way as an array (single dimension, zero-based).
indexPayload :: ArrayPayload -> Int -> Const
indexPayload payl i = 
  case payl of 
    ArrayPayloadInt    arr -> I   (arr `index` i)
    ArrayPayloadInt8   arr -> I8  (arr `index` i)
    ArrayPayloadInt16  arr -> I16 (arr `index` i)
    ArrayPayloadInt32  arr -> I32 (arr `index` i)
    ArrayPayloadInt64  arr -> I64 (arr `index` i)
    ArrayPayloadWord   arr -> W   (arr `index` i)
    ArrayPayloadWord8  arr -> W8  (arr `index` i)
    ArrayPayloadWord16 arr -> W16 (arr `index` i)
    ArrayPayloadWord32 arr -> W32 (arr `index` i)
    ArrayPayloadWord64 arr -> W64 (arr `index` i)
    ArrayPayloadFloat  arr -> F   (arr `index` i)
    ArrayPayloadDouble arr -> D   (arr `index` i)
    ArrayPayloadChar   arr -> C   (arr `index` i)
    ArrayPayloadBool   arr -> toBool (arr `index` i) 
    ArrayPayloadUnit   len -> if i < len && i >= 0
                              then Tup []
                              else error $ "indexPayload: out of bounds index ("
                                           ++show i++") into ArrayPayloadUnit of len "++show len
  where
    index a i = unsafePerformIO $ MA.readArray a i

-- | Apply a generic transformation to the Array Payload irrespective
--   of element type.  This is useful for rearranging or removing
--   elements of a payload without looking at the contents.
applyToPayload :: (forall a . RawData a -> RawData a) -> ArrayPayload -> ArrayPayload
applyToPayload fn payl = applyToPayload2 (\ a _ -> fn a) payl


-- | This is similar to `applyToPayload`, but also provides the ability for
--   the function passed in to inspect elements in the input array in a
--   generic fashion (as Const type).
applyToPayload2 :: (forall a . RawData a -> (Int -> Const) -> RawData a)
                -> ArrayPayload -> ArrayPayload
applyToPayload2 fn payl = 
  case payl of 
--    ArrayPayloadUnit       -> ArrayPayloadUnit
    ArrayPayloadInt    arr -> ArrayPayloadInt    (fn arr (\i -> I   (arr `index` i)))
    ArrayPayloadInt8   arr -> ArrayPayloadInt8   (fn arr (\i -> I8  (arr `index` i)))
    ArrayPayloadInt16  arr -> ArrayPayloadInt16  (fn arr (\i -> I16 (arr `index` i)))
    ArrayPayloadInt32  arr -> ArrayPayloadInt32  (fn arr (\i -> I32 (arr `index` i))) 
    ArrayPayloadInt64  arr -> ArrayPayloadInt64  (fn arr (\i -> I64 (arr `index` i)))
    ArrayPayloadWord   arr -> ArrayPayloadWord   (fn arr (\i -> W   (arr `index` i)))
    ArrayPayloadWord8  arr -> ArrayPayloadWord8  (fn arr (\i -> W8  (arr `index` i))) 
    ArrayPayloadWord16 arr -> ArrayPayloadWord16 (fn arr (\i -> W16 (arr `index` i)))
    ArrayPayloadWord32 arr -> ArrayPayloadWord32 (fn arr (\i -> W32 (arr `index` i)))
    ArrayPayloadWord64 arr -> ArrayPayloadWord64 (fn arr (\i -> W64 (arr `index` i)))
    ArrayPayloadFloat  arr -> ArrayPayloadFloat  (fn arr (\i -> F   (arr `index` i)))
    ArrayPayloadDouble arr -> ArrayPayloadDouble (fn arr (\i -> D   (arr `index` i)))
    ArrayPayloadChar   arr -> ArrayPayloadChar   (fn arr (\i -> C   (arr `index` i)))
    ArrayPayloadBool   arr -> ArrayPayloadBool -- Word8's represent bools
                              (fn arr (\i -> case arr `index` i of
                                               0 -> B False 
                                               _ -> B True))
    -- No values can actually change here.  WARNING: this plays fast and loose
    -- with error conditions.  In particular we should have to expose out-of-bounds access:
    ArrayPayloadUnit   len -> ArrayPayloadUnit len
  where
    index a i = unsafePerformIO $ MA.readArray a i


-- | This version allows the payload to be rebuilt as a list of Const,
--   which must all be the same type as the input.
applyToPayload3 :: (Int -> (Int -> Const) -> [Const]) -> ArrayPayload -> ArrayPayload
-- TODO!! The same-type-as-input restriction could be relaxed.
applyToPayload3 fn payl = 
  case payl of 
--    ArrayPayloadUnit       -> ArrayPayloadUnit
    ArrayPayloadInt    arr -> ArrayPayloadInt    (fromL (map unI  $ fn len (\i -> I   (arr `index` i))))
    ArrayPayloadInt8   arr -> ArrayPayloadInt8   (fromL (map unI8 $ fn len (\i -> I8  (arr `index` i))))
    ArrayPayloadInt16  arr -> ArrayPayloadInt16  (fromL (map unI16$ fn len (\i -> I16 (arr `index` i))))
    ArrayPayloadInt32  arr -> ArrayPayloadInt32  (fromL (map unI32$ fn len (\i -> I32 (arr `index` i))))
    ArrayPayloadInt64  arr -> ArrayPayloadInt64  (fromL (map unI64$ fn len (\i -> I64 (arr `index` i))))
    ArrayPayloadWord   arr -> ArrayPayloadWord   (fromL (map unW  $ fn len (\i -> W   (arr `index` i))))
    ArrayPayloadWord8  arr -> ArrayPayloadWord8  (fromL (map unW8 $ fn len (\i -> W8  (arr `index` i))))
    ArrayPayloadWord16 arr -> ArrayPayloadWord16 (fromL (map unW16$ fn len (\i -> W16 (arr `index` i))))
    ArrayPayloadWord32 arr -> ArrayPayloadWord32 (fromL (map unW32$ fn len (\i -> W32 (arr `index` i))))
    ArrayPayloadWord64 arr -> ArrayPayloadWord64 (fromL (map unW64$ fn len (\i -> W64 (arr `index` i))))
    ArrayPayloadFloat  arr -> ArrayPayloadFloat  (fromL (map unF  $ fn len (\i -> F   (arr `index` i))))
    ArrayPayloadDouble arr -> ArrayPayloadDouble (fromL (map unD  $ fn len (\i -> D   (arr `index` i))))
    ArrayPayloadChar   arr -> ArrayPayloadChar   (fromL (map unC  $ fn len (\i -> C   (arr `index` i))))
    ArrayPayloadBool   arr -> ArrayPayloadBool   (fromL (map fromBool$ fn len (\i -> toBool (arr `index` i))))
    ArrayPayloadUnit   len -> ArrayPayloadUnit len
  where 
   len       = payloadLength payl
   index a i = unsafePerformIO $ MA.readArray a i


-- Various helpers:
----------------------------------------
fromL l = unsafePerformIO $ MA.newListArray (0,length l - 1) l
toBool 0 = B False
toBool _ = B True
fromBool (B False) = 0
fromBool (B True)  = 1
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
unF oth = error$"unF, expected float, received: "++show oth
unD (D x) = x
unC (C x) = x
unB (B x) = x
unTup (Tup ls) = ls

arrLen :: Storable e => RawData e -> Int
arrLen arr = unsafePerformIO $ MA.rangeSize `fmap` MA.getBounds arr


-- | Apply an elementwise function to each Const inside an array.  The
--   mapped function must consistently map the same type of input
--   Const to the same type of output Const, or a runtime error will
--   be generated.
-- 
--   Note, this function must coalesce tuples-of-arrays into tuples of
--   elements before those elements can be passed to the mapped function.
mapArray :: (Const -> Const) -> AccArray -> AccArray
mapArray fn (AccArray sh [pl]) = 
  AccArray sh (mapPayload fn pl)

-- This case is more complicated.  Here's where the coalescing happens.
mapArray fn (AccArray sh pls) = 
  -- For the time being we fall back to an extremely inefficient
  -- system.  This function should only ever be really be used for
  -- non-performance-critical reference implemenatations.
  AccArray sh $ payloadsFromList1 $ 
  map fn $ 
  map Tup $ L.transpose $ map payloadToList pls

-- | Apply an elementwise function to a single payload.  The function
--   must consistently map the same type of input to the same type of
--   output `Const`.
-- 
--   The output for each precossed element may be a tuple, the number
--   of elements within that tuple determines how many `ArrayPayload`s
--   will reside in this function's output list.
mapPayload :: (Const -> Const) -> ArrayPayload -> [ArrayPayload]
mapPayload fn payl =   
--  tracePrint ("\nMapPayload of "++show payl++" was : ") $ 
  case payl of        
    ArrayPayloadInt   arr  -> rebuild (fn . I  $ arr `index` 0) (fn . I  ) arr
    ArrayPayloadInt8  arr  -> rebuild (fn . I8 $ arr `index` 0) (fn . I8 ) arr
    ArrayPayloadInt16 arr  -> rebuild (fn . I16$ arr `index` 0) (fn . I16) arr
    ArrayPayloadInt32 arr  -> rebuild (fn . I32$ arr `index` 0) (fn . I32) arr
    ArrayPayloadInt64 arr  -> rebuild (fn . I64$ arr `index` 0) (fn . I64) arr
    ArrayPayloadWord   arr -> rebuild (fn . W  $ arr `index` 0) (fn . W  ) arr
    ArrayPayloadWord8  arr -> rebuild (fn . W8 $ arr `index` 0) (fn . W8 ) arr
    ArrayPayloadWord16 arr -> rebuild (fn . W16$ arr `index` 0) (fn . W16) arr
    ArrayPayloadWord32 arr -> rebuild (fn . W32$ arr `index` 0) (fn . W32) arr
    ArrayPayloadWord64 arr -> rebuild (fn . W64$ arr `index` 0) (fn . W64) arr
    ArrayPayloadFloat  arr -> rebuild (fn . F  $ arr `index` 0) (fn . F) arr
    ArrayPayloadDouble arr -> rebuild (fn . D  $ arr `index` 0) (fn . D) arr
    ArrayPayloadChar   arr -> rebuild (fn . C  $ arr `index` 0) (fn . C) arr
    ArrayPayloadBool   arr -> rebuild (fn . W8 $ arr `index` 0) (fn . W8) arr
    ArrayPayloadUnit   len -> [ArrayPayloadUnit len]
  where
    index a i = unsafePerformIO $ MA.readArray a i

    
{-# INLINE rebuild #-}
rebuild :: Storable e' => Const -> (e' -> Const) -> RawData e' -> [ArrayPayload]
rebuild first fn arr = 
  case first of
    I   _ -> [ArrayPayloadInt    $ amap (unI   . fn) arr]
    I8  _ -> [ArrayPayloadInt8   $ amap (unI8  . fn) arr]    
    I16 _ -> [ArrayPayloadInt16  $ amap (unI16 . fn) arr]    
    I32 _ -> [ArrayPayloadInt32  $ amap (unI32 . fn) arr]    
    I64 _ -> [ArrayPayloadInt64  $ amap (unI64 . fn) arr]    
    W   _ -> [ArrayPayloadWord   $ amap (unW   . fn) arr]
    W8  _ -> [ArrayPayloadWord8  $ amap (unW8  . fn) arr]    
    W16 _ -> [ArrayPayloadWord16 $ amap (unW16 . fn) arr]    
    W32 _ -> [ArrayPayloadWord32 $ amap (unW32 . fn) arr]    
    W64 _ -> [ArrayPayloadWord64 $ amap (unW64 . fn) arr]        
    F   _ -> [ArrayPayloadFloat  $ amap (unF   . fn) arr]
    D   _ -> [ArrayPayloadDouble $ amap (unD   . fn) arr]
    C   _ -> [ArrayPayloadChar   $ amap (unC   . fn) arr]
    B   _ -> [ArrayPayloadBool   $ amap (unW8  . fn) arr]
    Tup [] -> [ArrayPayloadUnit $ arrLen arr]
    Tup ls -> concatMap (\ (i,x) -> rebuild x (\ x -> tupref (fn x) i) arr) $ 
              zip [0..] ls              
    oth -> error$"This constant should not be found inside an ArrayPayload: "++show oth
 where
   tupref (Tup ls) i = ls !! i

   amap f a = unsafePerformIO $ MA.mapArray f a


-- | Convert a list of `Const` scalars of the same type into one or
--   more `ArrayPayload`s.  Keep in mind that this is an inefficient
--   thing to do, and in performant code you should never convert
--   arrays to or from lists.
--   
--   The first argument is the exected element type.
--   
--   More than one `ArrayPayload` output is produced when the inputs
--   are tuple constants.
payloadsFromList :: Type -> [Const] -> [ArrayPayload]
payloadsFromList ty ls = 
  case ty of 
    TInt   -> [ArrayPayloadInt    $ fromL $ map unI   ls]
    TInt8  -> [ArrayPayloadInt8   $ fromL $ map unI8  ls]
    TInt16  -> [ArrayPayloadInt16  $ fromL $ map unI16 ls]
    TInt32  -> [ArrayPayloadInt32  $ fromL $ map unI32 ls]
    TInt64  -> [ArrayPayloadInt64  $ fromL $ map unI64 ls]
    TWord    -> [ArrayPayloadWord   $ fromL $ map unW   ls]
    TWord8   -> [ArrayPayloadWord8  $ fromL $ map unW8  ls]
    TWord16  -> [ArrayPayloadWord16 $ fromL $ map unW16 ls]
    TWord32  -> [ArrayPayloadWord32 $ fromL $ map unW32 ls]
    TWord64  -> [ArrayPayloadWord64 $ fromL $ map unW64 ls]
    TFloat  -> [ArrayPayloadFloat  $ fromL $ map unF   ls]
    TDouble -> [ArrayPayloadDouble $ fromL $ map unD   ls]
    TChar   -> [ArrayPayloadChar   $ fromL $ map unC   ls]
    TBool   -> [ArrayPayloadBool   $ fromL $ map fromBool ls]
    TTuple [] -> [ArrayPayloadUnit $ length ls]
    TTuple tys -> concatMap (uncurry payloadsFromList)                 
                            (zip tys (L.transpose $ map unTup ls))
    oth -> error$"payloadsFromList: This constant should not be found inside an ArrayPayload: "++show oth


-- | Same as `payloadsFromList` but requires that the list be non-empty and all
--   elements be the same type.  The type is inferred from the type of the contained
--   `Const`s.
payloadsFromList1 :: [Const] -> [ArrayPayload]
payloadsFromList1 [] = error "payloadFromList1: cannot convert empty list -- what are the type of its contents?"
payloadsFromList1 ls@(hd:_) = 
  case hd of 
    I   _ -> [ArrayPayloadInt    $ fromL $ map unI   ls]
    I8  _ -> [ArrayPayloadInt8   $ fromL $ map unI8  ls]
    I16 _ -> [ArrayPayloadInt16  $ fromL $ map unI16 ls]
    I32 _ -> [ArrayPayloadInt32  $ fromL $ map unI32 ls]
    I64 _ -> [ArrayPayloadInt64  $ fromL $ map unI64 ls]
    W   _ -> [ArrayPayloadWord   $ fromL $ map unW   ls]
    W8  _ -> [ArrayPayloadWord8  $ fromL $ map unW8  ls]
    W16 _ -> [ArrayPayloadWord16 $ fromL $ map unW16 ls]
    W32 _ -> [ArrayPayloadWord32 $ fromL $ map unW32 ls]
    W64 _ -> [ArrayPayloadWord64 $ fromL $ map unW64 ls]
    F   _ -> [ArrayPayloadFloat  $ fromL $ map unF   ls]
    D   _ -> [ArrayPayloadDouble $ fromL $ map unD   ls]
    C   _ -> [ArrayPayloadChar   $ fromL $ map unC   ls]
    B   _ -> [ArrayPayloadBool   $ fromL $ map fromBool ls]
    Tup [] -> [ArrayPayloadUnit $ length ls] -- FIXME: check the type of the whole list.
    Tup _ -> concatMap payloadsFromList1 $ 
             L.transpose $ map unTup ls
    oth -> error$"payloadsFromList1: This constant should not be found inside an ArrayPayload: "++show oth      

-- | Unpack a payload into a list of Const.  Inefficient!
payloadToList :: ArrayPayload -> [Const]
payloadToList payl =   
  case payl of        
    ArrayPayloadInt    arr -> map I  $ elems arr
    ArrayPayloadInt8   arr -> map I8 $ elems arr
    ArrayPayloadInt16  arr -> map I16$ elems arr
    ArrayPayloadInt32  arr -> map I32$ elems arr
    ArrayPayloadInt64  arr -> map I64$ elems arr
    ArrayPayloadWord   arr -> map W  $ elems arr
    ArrayPayloadWord8  arr -> map W8 $ elems arr
    ArrayPayloadWord16 arr -> map W16$ elems arr
    ArrayPayloadWord32 arr -> map W32$ elems arr
    ArrayPayloadWord64 arr -> map W64$ elems arr
    ArrayPayloadFloat  arr -> map F  $ elems arr
    ArrayPayloadDouble arr -> map D  $ elems arr
    ArrayPayloadChar   arr -> map C  $ elems arr
    ArrayPayloadBool   arr -> map toBool $ elems arr
    ArrayPayloadUnit   len -> L.replicate len (Tup [])
  where
    elems :: forall e. Storable e => RawData e -> [e]
    elems = unsafePerformIO . MA.getElems

-- | Get a `ForeignPtr` to the raw storage of an array.
--
-- PRECONDITION: The unboxed array must be pinned.    
payloadToPtr :: ArrayPayload -> Ptr ()
payloadToPtr payl = 
  case payl of        
    ArrayPayloadInt    arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadInt8   arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadInt16  arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadInt32  arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadInt64  arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadWord   arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadWord8  arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadWord16 arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadWord32 arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadWord64 arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadFloat  arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadDouble arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadChar   arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadBool   arr -> castPtr $ storableArrayPtr arr
    ArrayPayloadUnit   _   -> error "payloadToPtr: cannot work for an ArrayPayloadUnit"

-- | Copy from foreign memory (O(N)) to reconstruct a payload with the given type and
-- number of *elements* (not bytes).  The bytesize is determined based on the type
-- argument supplied.
--
-- TODO: This can be replaced with an O(1) operation if we make sure to always
-- allocate space for results within Haskell as UArrays.
payloadFromPtr :: Type -> Int -> Ptr Word8 -> IO ArrayPayload
payloadFromPtr ty len srcPtr =
  case ty of 
    TInt    -> ArrayPayloadInt    <$> arr
    TInt8   -> ArrayPayloadInt8   <$> arr
    TInt16  -> ArrayPayloadInt16  <$> arr
    TInt32  -> ArrayPayloadInt32  <$> arr
    TInt64  -> ArrayPayloadInt64  <$> arr
    TWord   -> ArrayPayloadWord   <$> arr
    TWord8  -> ArrayPayloadWord8  <$> arr
    TWord16 -> ArrayPayloadWord16 <$> arr
    TWord32 -> ArrayPayloadWord32 <$> arr
    TWord64 -> ArrayPayloadWord64 <$> arr
    TFloat  -> ArrayPayloadFloat  <$> arr
    TDouble -> ArrayPayloadDouble <$> arr
    TChar   -> ArrayPayloadChar   <$> arr
    TBool   -> ArrayPayloadBool   <$> arr
    TTuple [] -> return (ArrayPayloadUnit len)
    -- TTuple tys -> concatMap (uncurry payloadsFromList)                 
    --                         (zip tys (L.transpose $ map unTup ls))
    _ -> error$"payloadFromPtr: Unexpected array type: "++show ty
  where
    arr :: forall elt . Storable elt => IO (RawData elt)
    arr = do  let bytes = len * sizeOf (undefined::elt)
              maybtrace (" [dbg] !! Copying back "++show bytes++" bytes (array len "++show len++") into haskell heap!" )$return()
              fp <- mallocForeignPtrArray len
              withForeignPtr fp $ \dstPtr -> copyArray dstPtr (castPtr srcPtr) len
              return $ StorableArray 0 (len-1) len fp


-- Obtains a pointer to the payload of an storable array.
--
{-# INLINE storableArrayPtr #-}
storableArrayPtr :: StorableArray i a -> Ptr a
storableArrayPtr (StorableArray _ _ _ fp) = unsafeForeignPtrToPtr fp

-- | Create an array of with the given dimensions and many copies of
--   the same element.  This deals with constructing the appropriate
--   type of payload to match the type of constant (which is otherwise
--   a large case statement).
replicate :: [Int] -> Const -> AccArray 
replicate dims const = AccArray dims (payload const)
  where 
    len = foldl (*) 1 dims
    payload const = 
     case const of 
       I   x -> [ArrayPayloadInt   (fromL$ Prelude.replicate len x)]
       I8  x -> [ArrayPayloadInt8  (fromL$ Prelude.replicate len x)]
       I16 x -> [ArrayPayloadInt16 (fromL$ Prelude.replicate len x)]
       I32 x -> [ArrayPayloadInt32 (fromL$ Prelude.replicate len x)]
       I64 x -> [ArrayPayloadInt64 (fromL$ Prelude.replicate len x)]
       W   x -> [ArrayPayloadWord   (fromL$ Prelude.replicate len x)]
       W8  x -> [ArrayPayloadWord8  (fromL$ Prelude.replicate len x)]       
       W16 x -> [ArrayPayloadWord16 (fromL$ Prelude.replicate len x)]
       W32 x -> [ArrayPayloadWord32 (fromL$ Prelude.replicate len x)]
       W64 x -> [ArrayPayloadWord64 (fromL$ Prelude.replicate len x)]
       F x -> [ArrayPayloadFloat  (fromL$ Prelude.replicate len x)]
       D x -> [ArrayPayloadDouble (fromL$ Prelude.replicate len x)]
       C x -> [ArrayPayloadChar   (fromL$ Prelude.replicate len x)]
       B x -> [ArrayPayloadBool   (fromL$ Prelude.replicate len (fromBool const))]
       Tup [] -> [ArrayPayloadUnit len]
       Tup ls -> concatMap payload ls 
-- TODO -- add all C array types to the ArrayPayload type:
--            | CF CFloat   | CD CDouble 
--            | CS  CShort  | CI  CInt  | CL  CLong  | CLL  CLLong
--            | CUS CUShort | CUI CUInt | CUL CULong | CULL CULLong
--            | CC  CChar   | CSC CSChar | CUC CUChar 


-- | An AccArray stores an array of tuples.  This function reports how
--   many components there are in the stored tuples (one or more).
numComponents :: AccArray -> Int
numComponents (AccArray _ payloads) = length payloads


-- | Split one component (the first) out of an AccArray which
--   represents an array of tuples.  This returns two new AccArrays,
--   the first of which is a scalar, and the second of which contains
--   all remaining components.
-- 
--   If there are less than two components, this function raises a
--   runtime error.
splitComponent :: AccArray -> (AccArray, AccArray)
splitComponent (AccArray sh (h1:h2:rst)) = 
  (AccArray sh [h1], AccArray sh (h2:rst))
splitComponent x@(AccArray _ ls) = 
  error$ "splitComponent: input array has only "++show(length ls)++
         " components, needs at least two:\n   "++ show x



-- | Dereference an element from an AccArray.
-- 
-- This uses the most basic possible representation of
-- multidimensional indices, namely "[Int]"
-- 
-- Note that these indices are the REVERSE of the Accelerate source
-- representation.  Fastest varying index is the LEFTMOST.
indexArray ::  AccArray -> [Int] -> Const
-- Index into a Scalar:
indexArray (AccArray dims payloads) ind | length ind /= length dims = 
  error$"indexArray: array dimensions were "++show dims++" but index was of different length: "++ show ind
indexArray (AccArray []   payloads) []  = tuple $ map (`indexPayload` 0)        payloads
indexArray (AccArray dims payloads) ind = 
     maybtrace ("[dbg] Indexing array "++show ind++" multipliers "++show multipliers++" pos "++show position
                ++" array:\n          "++show (AccArray dims payloads)) $ 
     tuple $ map (`indexPayload` position) payloads
  where 
    -- How many elements do we per increment of this dimension?  Rightmost is fastest changing.
    -- multipliers = scanr (*) 1 (init dims) -- The rightmost gets a 1 multiplier.
    multipliers = scanl (*) 1 (tail dims) -- The leftmost gets a 1 multiplier.
    position = sum $ zipWith (*) multipliers ind

-- Private helper
tuple :: [Const] -> Const
tuple [x] = x
tuple ls  = Tup ls

-- | Take a list of arrays of equal shape and concat them into a single AccArray.  
concatAccArrays :: [S.AccArray] -> S.AccArray
concatAccArrays [] = error "concatAccArrays: Cannot zip an empty list of AccArrays (don't know dimension)"
concatAccArrays origls = 
  maybtrace (" [dbg] concatAccArrays: dims "++show dims++", lens "++show lens) $ 
  if not (allSame lens)
  then error$"concatAccArrays: mismatch in lengths: "++show lens
  else if not (allSame dims)
       then error$"concatAccArrays: mismatch in dims: "++show dims
       else S.AccArray (head dims) payls
 where 
  lens = L.map payloadLength payls
  payls = concat paylss
  (dims,paylss) = unzip [ (dim,payls) | S.AccArray dim payls <- origls ] 
  allSame (hd:tl) = all (==hd) tl
  allSame []      = True


-- | Returns an error message if anything is wrong.  In particular, the number and
--   type of payloads should match the declared type.  Note that an AccArray
--   represents a single logical array with one shape (though it can be an array of
--   tuples).
verifyAccArray :: Type -> AccArray -> Maybe ErrorMsg
verifyAccArray ty (AccArray shp cols) =
  case ty of
    TArray d elt ->
      let expectedCols = flattenTy elt in -- FIXME: handling units..
      re$ unlines $ catMaybes $      
      ((if d /= length shp
        then Just$"AccArray shape "++show shp++" doesn't match dimension in type: "++show d
        else Nothing) :
       (if length expectedCols /= length cols
       then Just$"Bad AccArray.  Unexpected number of payloads ("++
            show(length cols)++") for type "++show ty
       else Nothing) :
       (tag$zipWith (assertEq "Payload type")
                    (map payloadToType cols) expectedCols) ++
       (tag$zipWith (assertEq "Payload length")
                     (map payloadLength cols) (repeat expectedSize)))
    oth -> Just$ "AccArray had non-array type: "++show oth
 where
   expectedSize = product shp
   re ""  = Nothing
   re str = Just str   
   mismatchErr msg got expected = msg++" does not match expected. "++
                                  "\nGot:      "++show got ++
                                  "\nExpected: "++show expected
   assertEq msg got expected =
     if got == expected
     then Nothing
     else Just(mismatchErr msg got expected)
   -- Enhance the message with more info:       
   tag  = map (fmap 
               (++"\nAccArray contents: "++
                unlines (map ((take 70) . show) cols)))


-- | Some backends end up with a flatter representation than they want after
-- flattening out both array level tuples and scalar tuples /inside/ arrays.
-- 
-- Given an [overly] flat list of "singleton" AccArrays, this does a type-guided
-- repackaging to produce a, possibly shorter, list of AccArrays that reassociate the
-- individual components of an array-of-tuples.
-- 
-- The result should match the provided type (or an error is thrown).
reglueArrayofTups :: S.Type -> [S.AccArray] -> [S.AccArray]
reglueArrayofTups ty0 ls0 = 
--   trace ("reglueArrayofTups "++show (ty0,ls0)++" -> "++show result) $ 
   result
  where 
   result = case ty0 of 
             TTuple tys -> loop tys   ls0
             oth        -> loop [oth] ls0
   notEnough = error $ "reglueArrayofTups: not enough payloads to fulfill type "++show ty0++": "++show ls0

   -- Make sure NOT to squish units...
   myflatten :: Type -> [Type]
   myflatten (TTuple [])  = [TTuple []]
   myflatten (TTuple ls)  = concatMap myflatten ls
   myflatten         ty  = [ty]

   loop [] [] = [] -- Victory
   loop _  [] = notEnough
   loop [] _  = error $ "reglueArrayofTups: too many payloads ("++show(length ls0)
                        ++") to fulfill type "++show ty0++": "++(take 160$ show ls0)
   loop (TArray dim elt : tys) arrs = 
      let scalars  = myflatten elt 
          expected = length scalars
          (batch,rest) = splitAt expected arrs 
      in
      -- trace ("reglueArrayofTups: got batch "++show (scalars, (batch,rest))) $ 
      if expected == 0 
      then error$"reglueArrayofTups: internal invariant broken, why does this array need zero values?: "++show (TArray dim elt)
      else if length batch /= expected then notEnough else 
       case batch of
         [] -> notEnough
         (AccArray dims0 [payload0] : rst ) -> 
          let payloads = reverse $ 
                     foldl (\ acc (S.AccArray dims1 [payl]) -> 
                              if dims0 == dims1 
                              then payl:acc
                              else error$"reglueArrayofTups: two arrays to be zipped have different dims: "
                                         ++show dims0++", vs "++show dims1)
                           [payload0] rst
          in AccArray dims0 payloads 
             : loop tys rest

   loop (TTuple ls1 : ls2) arrs = loop (ls1++ls2) arrs
   loop ls arrs = error $ "reglueArrayofTups: got a non-array type in list: " ++show ls


type ErrorMsg = String


--------------------------------------------------------------------------------
-- Partitioning arrays:

-- | Split an AccArray into K pieces along the outermost dimension.  The outermost
-- dimension corresponds to cutting the actual memory buffers into even (contiguous)
-- pieces.
-- 
-- If the size of the array does not divide evenly, the last parttion gets the extra
-- data.
splitAccArray :: Int -> AccArray -> [AccArray]
splitAccArray pieces (AccArray dims payls) 
  | pieces < 1 = error $"splitAccArray: Cannot split into less than one piece: "++show pieces
  | qt < 1 = error$ "AccArray of dimensions "++show dims++" cannot be split into "++show pieces++" pieces along outer (last) dim!"
  | otherwise = 
    -- trace ("splitAccArray, "++show (size,qt,rem,rest,outer)) $ 
    zipWith AccArray allDims $ 
    L.transpose $ 
    map (splitPayload size pieces) payls
 where
  allDims     = L.replicate (pieces-1) newDims ++ [newDimsLast]
  newDims     = rest ++ [qt]
  newDimsLast = rest ++ [qt+rem]
  size = qt * product rest
  (qt,rem) = outer `quotRem` pieces
  (rest,outer) = splitLast dims

splitPayload :: Int -> Int -> ArrayPayload -> [ArrayPayload]
splitPayload n k payl =   
  -- tracePrint ("\nsplitPayload of "++show payl++" was : ") $ 
  case payl of
    ArrayPayloadInt  arr  -> map ArrayPayloadInt   $ splitArrays n k arr
    ArrayPayloadInt8  arr -> map ArrayPayloadInt8  $ splitArrays n k arr 
    ArrayPayloadInt16 arr -> map ArrayPayloadInt16 $ splitArrays n k arr 
    ArrayPayloadInt32 arr -> map ArrayPayloadInt32 $ splitArrays n k arr 
    ArrayPayloadInt64 arr -> map ArrayPayloadInt64 $ splitArrays n k arr 
    ArrayPayloadWord   arr -> map ArrayPayloadWord $ splitArrays n k arr 
    ArrayPayloadWord8  arr -> map ArrayPayloadWord8 $ splitArrays n k arr 
    ArrayPayloadWord16 arr -> map ArrayPayloadWord16 $ splitArrays n k arr  
    ArrayPayloadWord32 arr -> map ArrayPayloadWord32 $ splitArrays n k arr  
    ArrayPayloadWord64 arr -> map ArrayPayloadWord64 $ splitArrays n k arr  
    ArrayPayloadFloat  arr -> map ArrayPayloadFloat $ splitArrays n k arr  
    ArrayPayloadDouble arr -> map ArrayPayloadDouble $ splitArrays n k arr  
    ArrayPayloadChar   arr -> map ArrayPayloadChar $ splitArrays n k arr 
    ArrayPayloadBool   arr -> map ArrayPayloadBool $ splitArrays n k arr 
    ArrayPayloadUnit   len -> let (q,r) = quotRem len n in 
                              (L.replicate (q-1) (ArrayPayloadUnit n))
                              ++ [ArrayPayloadUnit (n+r)]

-- | Takes a specific chunksize for the output partitions. 
--   Any elements left over go in the final array.
splitArrays
    :: Storable elt
    => Int
    -> Int
    -> RawData elt
    -> [RawData elt]
splitArrays size howmany arr =
  -- trace(" CUTTING ARRAY, bounds "++show(low,high)++", size "++show size++", quotRem: "++show (howmany,leftover))$
  [ fromL s | s <- cut (howmany-1) xs ]
  where
    xs          = unsafePerformIO $ MA.getElems arr
    cut 0 r     = [r]
    cut n r     = let (x,y) = splitAt size r
                  in  x : cut (n-1) y


-- Scratch:
t0 :: RawData Int
t0 = fromL [1..12]

t0b :: AccArray 
-- t0b = AccArray [3,2,2] [ArrayPayloadInt t0, ArrayPayloadInt t0]
t0b = AccArray [2,2,3] [ArrayPayloadInt t0, ArrayPayloadInt t0]

p0 = splitAccArray 2 t0b
v0 = map (verifyAccArray (TArray 3 (TTuple [TInt,TInt]))) p0

t1 :: RawData Char
t1 = fromL ['a'..'j']

p1 = splitArrays 5 2 t1

go :: IO ()
go = 
  case t0 of 
    StorableArray l u nn _fp -> 
      putStrLn $ "HMM "++show (l,u,nn)

-- last and init functions together.  I wonder if it's actually faster.
splitLast :: [a] -> ([a], a)
splitLast [] = error "splitLast: given null list"
splitLast [x] = ([],x)
splitLast (h:tl) = let (r,x) = splitLast tl in (h:r,x)

  

