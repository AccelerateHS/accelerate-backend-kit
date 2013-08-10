{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A library for the runtime construction of fully typed Accelerate programs.

module Data.Array.Accelerate.DynamicAcc2
{-
       (-- * Dynamically typed AST pieces
         SealedExp, SealedAcc,
         
         -- * Runtime representation of Types and Constants:
         Type(..), Const(..),

         -- * Syntax-constructing functions
         constantD, useD, 
         unitD, mapD, 

         -- * Functions to convert `SimpleAcc` programs into fully-typed Accelerate
         --   programs.
         convertExp, convertClosedExp,

         t0, t1, t2  -- TEMP
       )
-}
       where

import           Data.Array.Accelerate as A
import           Data.Array.Accelerate.Tuple
import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Smart as Sm
import qualified Data.Array.Accelerate.Type as T
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                 (Type(..), Const(..), AVar, Var, Prog(..), 
                  Prim(..), NumPrim(..), IntPrim(..), FloatPrim(..))
import           Data.Array.Accelerate.BackendKit.Tests (allProgsMap, p1a, TestEntry(..))
import           Data.Array.Accelerate.BackendKit.SimpleArray (payloadsFromList1)
-- import Data.Array.Accelerate.Interpreter as I
-- import           Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone (repackAcc)
import           Data.Array.Accelerate.BackendKit.Phase1.ToAccClone (repackAcc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.Array.Data  as Dat

import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone as Cvt (accToAccClone, expToExpClone)

import Data.Bits as B
import Data.Typeable (gcast)
import Data.Dynamic (Dynamic, fromDyn, fromDynamic, toDyn,
                     Typeable, Typeable3, mkTyConApp, TyCon, mkTyCon3, typeOf3, typeOf)
import Data.Map as M
import Prelude as P
import Data.Maybe (fromMaybe, fromJust)
-- import Data.Word
import Debug.Trace (trace)
-- import Control.Exception (bracket)
-- import Control.Monad (when)

import qualified Data.Array.Unboxed as U

------------------------------------------------------------------------------------------


-- INCOMPLETE: In several places we have an incomplete pattern match
-- due to no Elt instances for C types: [2013.08.09]
#define CTYERR error "DynamicAcc: Could not handle CType, it is not in Elt yet!"
#define INSERT_CTY_ERR_CASES \
  TCFloat  -> CTYERR; \
  TCDouble -> CTYERR; \
  TCShort  -> CTYERR; \
  TCInt    -> CTYERR; \
  TCLong   -> CTYERR; \
  TCLLong  -> CTYERR; \
  TCUShort  -> CTYERR; \
  TCUInt    -> CTYERR; \
  TCULong   -> CTYERR; \
  TCULLong  -> CTYERR; \
  TCChar    -> CTYERR; \
  TCSChar   -> CTYERR; \
  TCUChar   -> CTYERR; \

--------------------------------------------------------------------------------
-- AST Representations
--------------------------------------------------------------------------------

-- TODO: make these pairs that keep around some printed rep for debugging purposes in
-- the case of a downcast error.  Also make them newtypes!
newtype SealedExp     = SealedExp     Dynamic deriving Show
newtype SealedOpenExp = SealedOpenExp Dynamic deriving Show
newtype SealedAcc     = SealedAcc     Dynamic deriving Show

sealExp :: Typeable a => A.Exp a -> SealedExp
sealExp = SealedExp . toDyn

sealAcc :: Typeable a => Acc a -> SealedAcc
sealAcc = SealedAcc . toDyn

downcastE :: forall a . Typeable a => SealedExp -> A.Exp a
downcastE (SealedExp d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
      error$"Attempt to unpack SealedExp with type "++show d
         ++ ", expected type Exp "++ show (toDyn (unused::a))

downcastA :: forall a . Typeable a => SealedAcc -> Acc a
downcastA (SealedAcc d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
       error$"Attempt to unpack SealedAcc with type "++show d
          ++ ", expected type Acc "++ show (toDyn (unused::a))

-- | Convert a `SimpleAcc` constant into a fully-typed (but sealed) Accelerate one.
constantE :: Const -> SealedExp

#define SEALIT(pat) pat x -> sealExp (A.constant x); 
#define ERRIT(pat) pat x -> error$"constantE: Accelerate is missing Elt instances for C types presently: "++show x;
constantE c =
  case c of {
    SEALIT(I) SEALIT(I8) SEALIT(I16) SEALIT(I32) SEALIT(I64)
    SEALIT(W) SEALIT(W8) SEALIT(W16) SEALIT(W32) SEALIT(W64)
    SEALIT(F) SEALIT(D)
    SEALIT(B)
    ERRIT(CS) ERRIT(CI) ERRIT(CL) ERRIT(CLL)
    ERRIT(CUS) ERRIT(CUI) ERRIT(CUL) ERRIT(CULL)
    ERRIT(C) ERRIT(CC) ERRIT(CSC) ERRIT(CUC)    
    ERRIT(CF) ERRIT(CD)
    Tup [] -> sealExp $ A.constant ();
    Tup ls -> error$ "constantE: Cannot handle tuple constants!  These should be ETuple's: "++show c 
  }

--------------------------------------------------------------------------------
-- Type representations
--------------------------------------------------------------------------------                

-- | We enhance "Data.Array.Accelerate.Type.TupleType" with Elt constraints.
data EltTuple a where
  UnitTuple   ::                                               EltTuple ()
  SingleTuple :: (Elt a)        => T.ScalarType a           -> EltTuple a
  PairTuple   :: (Elt a, Elt b) => EltTuple a -> EltTuple b -> EltTuple (a, b)
 deriving Typeable

-- | This GADT allows monomorphic value to carry a type inside.
data SealedEltTuple where
  SealedEltTuple :: (Typeable a, Elt a) =>
                    EltTuple a -> SealedEltTuple

-- | This is a bottle in which to store a type that satisfyies the Array class.
data SealedArrayType where
  -- Do we care about the ArrayElt class here?
  SealedArrayType :: Arrays a => Phantom a -> SealedArrayType

-- | Tuples of arrays rather than scalar `Elt`s.
data ArrTuple a where
  UnitTupleA   ::                                                     ArrTuple ()
  SingleTupleA :: Arrays a             => Phantom a                -> ArrTuple a
  PairTupleA   :: (Arrays a, Arrays b) => ArrTuple a -> ArrTuple b -> ArrTuple (a, b)

-- TODO: CAN WE PHASE OUT SealedArrayType in favor of SealedArrTuple?
data SealedArrTuple where
  SealedArrTuple :: ArrTuple a -> SealedArrTuple

-- | Accelerate shape types, sealed up.
data SealedShapeType where
  -- Do we care about the ArrayElt class here?
  SealedShapeType :: Shape sh => Phantom sh -> SealedShapeType

-- | Just a simple signal that the value is not used, only the type.
data Phantom a = Phantom a deriving Show

-- | Almost dependent types!  Dynamically construct a type in a bottle
-- that is isomorphic to an input value.  It can be opened up and used
-- as a goal type when repacking array data or returning an Acc
-- computation.
arrayTypeD :: Type -> SealedArrayType
arrayTypeD (TArray ndim elty) =
  case shapeTypeD ndim of
    SealedShapeType (_ :: Phantom sh) ->      
#define ATY(t1,t2) t1 -> SealedArrayType (Phantom(unused:: Array sh t2));
     case elty of {
       ATY(TInt,Int) ATY(TInt8,Int8) ATY(TInt16,Int16) ATY(TInt32,Int32) ATY(TInt64,Int64) 
       ATY(TWord,Word) ATY(TWord8,Word8) ATY(TWord16,Word16) ATY(TWord32,Word32) ATY(TWord64,Word64) 
       ATY(TFloat,Float) ATY(TDouble,Double)
       ATY(TChar,Char) ATY(TBool,Bool)

       INSERT_CTY_ERR_CASES

       TTuple ls -> (case scalarTypeD elty of 
                      SealedEltTuple (et :: EltTuple etty) -> 
                       SealedArrayType (Phantom(unused:: Array sh etty)));
       TArray _ _ -> error$"arrayTypeD: nested array type, not allowed in Accelerate: "++show(TArray ndim elty)
     }
arrayTypeD x@(TTuple _) = error$"arrayTypeD: does not handle tuples of arrays yet: "++show x
arrayTypeD oth = error$"arrayTypeD: expected array type, got "++show oth

-- | Construct a Haskell type from an Int!  Why not?
shapeTypeD :: Int -> SealedShapeType
shapeTypeD 0 = SealedShapeType (Phantom Z)
shapeTypeD n | n < 0 = error "shapeTypeD: Cannot take a negative number!"
shapeTypeD n =
  case shapeTypeD (n-1) of
    SealedShapeType (Phantom x :: Phantom sh) ->
      SealedShapeType (Phantom (x :. (unused::Int)))

-- | Convert the runtime, monomorphic type representation into a sealed container
-- with the true Haskell type inside.
scalarTypeD :: Type -> SealedEltTuple
scalarTypeD ty =
  case ty of
    TInt    -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int)
    TInt8   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int8)
    TInt16  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int16)
    TInt32  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int32)
    TInt64  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Int64)    
    TWord    -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word)
    TWord8   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word8)
    TWord16  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word16)
    TWord32  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word32)
    TWord64  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Word64)
    TFloat   -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Float)
    TDouble  -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Double)    
    TBool    -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Bool)
    TChar    -> SealedEltTuple$ SingleTuple (T.scalarType :: T.ScalarType Char)

    INSERT_CTY_ERR_CASES

    TTuple []    -> SealedEltTuple UnitTuple
    TTuple (hd:tl) ->
      case (scalarTypeD hd, scalarTypeD (TTuple tl)) of
        (SealedEltTuple (et1 :: EltTuple a),
         SealedEltTuple (et2 :: EltTuple b)) ->
          SealedEltTuple$ PairTuple et1 et2
    TArray {} -> error$"scalarTypeD: expected scalar type, got "++show ty


--------------------------------------------------------------------------------
-- AST Construction
--------------------------------------------------------------------------------


-- | Dynamically typed variant of `Data.Array.Accelerate.unit`.
unitD :: SealedEltTuple -> SealedExp -> SealedAcc
unitD elt exp =
  case elt of
    SealedEltTuple (t :: EltTuple et) ->
      case t of
        UnitTuple -> sealAcc$ unit$ constant ()
        SingleTuple (_ :: T.ScalarType s) ->
          sealAcc$ unit (downcastE exp :: A.Exp  s)
        PairTuple (_ :: EltTuple l) (_ :: EltTuple r) ->
          sealAcc$ unit (downcastE exp :: A.Exp  (l,r))

-- | Dynamically-typed variant of `Data.Array.Accelerate.use`.  However, this version
-- is less powerful, it only takes a single, logical array, not a tuple of arrays.
useD :: S.AccArray -> SealedAcc
useD arr =
  case sty of
    SealedArrayType (Phantom (_ :: aT)) ->
      sealAcc$ A.use$
      repackAcc (unused::Acc aT) [arr]
 where
   dty = S.accArrayToType arr
   sty = arrayTypeD dty

mapD :: (SealedExp -> SealedExp) -> SealedAcc ->
        S.Type -> S.Type -> SealedAcc 
mapD bodfn sealedInArr inArrTy outElmTy = 
      let 
          (TArray dims inty) = inArrTy 
          newAty = arrayTypeD (TArray dims outElmTy)
      in
       case (shapeTypeD dims, scalarTypeD inty, scalarTypeD outElmTy) of
         (SealedShapeType (_ :: Phantom shp), 
          SealedEltTuple (inET  :: EltTuple inT),
          SealedEltTuple (outET :: EltTuple outT)) ->
          let
            rawfn :: Exp inT -> Exp outT
            rawfn x = downcastE (bodfn (sealExp x))
            realIn :: Acc (Array shp inT)
            realIn = downcastA sealedInArr
          in
           -- Here we suffer PAIN to recover the Elt/Typeable instances:
           case (inET, outET) of
             (UnitTuple,     UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (PairTuple _ _, UnitTuple)     -> sealAcc $ A.map rawfn realIn
             (UnitTuple,     SingleTuple _) -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, SingleTuple _) -> sealAcc $ A.map rawfn realIn             
             (PairTuple _ _, SingleTuple _) -> sealAcc $ A.map rawfn realIn
             (UnitTuple,     PairTuple _ _) -> sealAcc $ A.map rawfn realIn
             (SingleTuple _, PairTuple _ _) -> sealAcc $ A.map rawfn realIn             
             (PairTuple _ _, PairTuple _ _) -> sealAcc $ A.map rawfn realIn


foldD :: (SealedExp -> SealedExp -> SealedExp) -> SealedExp -> SealedAcc ->
         S.Type -> SealedAcc 
foldD bodfn initE sealedInArr inArrTy = 
      let (TArray dims inty) = inArrTy
          -- Knock off one dimension:
          newAty = arrayTypeD (TArray (dims - 1) inty)
      in
       case (shapeTypeD (dims - 1), scalarTypeD inty) of
         (SealedShapeType (_ :: Phantom shp), 
          SealedEltTuple (inET  :: EltTuple inT)) ->
           let
               rawfn :: Exp inT -> Exp inT -> Exp inT
               rawfn x y = downcastE (bodfn (sealExp x) (sealExp y))
               realIn :: Acc (Array (shp :. Int) inT)
               realIn = downcastA sealedInArr
               init :: Exp inT
               init = downcastE initE
           in
            case inET of
              (UnitTuple    )     -> sealAcc $ A.fold rawfn init realIn
              (SingleTuple _)     -> sealAcc $ A.fold rawfn init realIn
              (PairTuple _ _)     -> sealAcc $ A.fold rawfn init realIn
  

--------------------------------------------------------------------------------
-- TODO: These conversion functions could move to their own module:
--------------------------------------------------------------------------------

-- | Track the scalar, array environment, and combined, fast-access environment.
data EnvPack = EnvPack [(Var,Type)] [(AVar,Type)]
                 (M.Map Var (Type, Either SealedExp SealedAcc))

expectEVar :: Either SealedExp SealedAcc -> SealedExp
expectEVar (Left se)  = se
expectEVar (Right sa) = error$"expected scalar variable, got variable bound to: "++show sa

expectAVar :: Either SealedExp SealedAcc -> SealedAcc
expectAVar (Left se)  = error$"expected array variable, got variable bound to: "++show se
expectAVar (Right sa) = sa

emptyEnvPack :: EnvPack 
emptyEnvPack = EnvPack [] [] M.empty 

-- | New array binding
extendA :: AVar -> Type -> SealedAcc -> EnvPack -> EnvPack 
extendA avr ty sld (EnvPack eS eA mp) =
  EnvPack eS ((avr,ty):eA)
          (M.insert avr (ty,Right sld) mp)

extendE :: Var -> Type -> SealedExp -> EnvPack -> EnvPack 
extendE vr ty sld (EnvPack eS eA mp) =
  EnvPack ((vr,ty):eS) eA
          (M.insert vr (ty,Left sld) mp)

type AENV0 = ()


-- | Convert an entire `SimpleAcc` expression into a fully-typed (but sealed) Accelerate one.
--   Requires a type environments for the (open) `SimpleAcc` expression:    
--   one for free expression variables, one for free array variables.
--     
convertExp :: EnvPack -> S.Exp -> SealedExp
convertExp ep@(EnvPack envE envA mp)
--           slayout@(SealedLayout (lyt :: Layout env0 env0'))
           ex =
  trace("Converting exp "++show ex++" with env "++show mp++" and dyn env "++show (envE,envA))$
  let cE = convertExp ep
      typeEnv = M.map P.fst mp -- Strip out the SealedExp/Acc bits leaving just the types.
  in 
  case ex of
    S.EConst c -> constantE c

    -- This is tricky, because it needs to become a deBruin index ultimately...
    -- Or we need to stay at the level of HOAS...
    S.EVr vr -> let (_,se) = mp # vr in expectEVar se

-- FINISHME:
    -- S.EShape _          -> undefined
    -- S.EShapeSize _      -> undefined
    -- S.EIndex _          -> undefined
    -- S.EIndexScalar _ _  -> undefined
    -- S.ETupProject {S.indexFromRight, S.projlen, S.tupexpr} -> undefined
    
    S.ETuple []    -> constantE (Tup [])
    S.ETuple [ex]  -> convertExp ep ex
    S.ETuple [a,b] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          a' = convertExp ep a
          b' = convertExp ep b
      in 
      case (scalarTypeD ta, scalarTypeD tb) of
        (SealedEltTuple (et1 :: EltTuple aty),
         SealedEltTuple (et2 :: EltTuple bty)) ->
          sealExp$ Sm.tup2 (downcastE a' :: Exp aty,
                            downcastE b' :: Exp bty)

    -- <EXTREME PAIN>
    -------------------------------------------------------------------------------
    S.ETuple [a,b,c] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c          
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc) of
          (SealedEltTuple (et1 :: EltTuple aty),
           SealedEltTuple (et2 :: EltTuple bty),
           SealedEltTuple (et3 :: EltTuple cty)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple [a,b,c,d] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          td = S.recoverExpType typeEnv d
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c
          d' = convertExp ep d               
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc, scalarTypeD td) of
          (SealedEltTuple (et1 :: EltTuple aty),
           SealedEltTuple (et2 :: EltTuple bty),
           SealedEltTuple (et3 :: EltTuple cty),
           SealedEltTuple (et4 :: EltTuple dty)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty,dty))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                      `SnocTup` (downcastE d' :: Exp dty)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty,dty)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple [a,b,c,d,e] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          td = S.recoverExpType typeEnv d
          te = S.recoverExpType typeEnv e          
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c
          d' = convertExp ep d
          e' = convertExp ep e          
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc, scalarTypeD td,
               scalarTypeD te) of
          (SealedEltTuple (_ :: EltTuple aty),
           SealedEltTuple (_ :: EltTuple bty),
           SealedEltTuple (_ :: EltTuple cty),
           SealedEltTuple (_ :: EltTuple dty),
           SealedEltTuple (_ :: EltTuple ety)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty,dty,ety))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                      `SnocTup` (downcastE d' :: Exp dty)
                      `SnocTup` (downcastE e' :: Exp ety)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty,dty,ety)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple [a,b,c,d,e,f] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          td = S.recoverExpType typeEnv d
          te = S.recoverExpType typeEnv e
          tf = S.recoverExpType typeEnv f
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c
          d' = convertExp ep d
          e' = convertExp ep e
          f' = convertExp ep f
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc, scalarTypeD td,
               scalarTypeD te, scalarTypeD tf) of
          (SealedEltTuple (_ :: EltTuple aty),
           SealedEltTuple (_ :: EltTuple bty),
           SealedEltTuple (_ :: EltTuple cty),
           SealedEltTuple (_ :: EltTuple dty),
           SealedEltTuple (_ :: EltTuple ety),
           SealedEltTuple (_ :: EltTuple fty)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty,dty,ety,fty))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                      `SnocTup` (downcastE d' :: Exp dty)
                      `SnocTup` (downcastE e' :: Exp ety)
                      `SnocTup` (downcastE f' :: Exp fty)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty,dty,ety,fty)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple [a,b,c,d,e,f,g] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          td = S.recoverExpType typeEnv d
          te = S.recoverExpType typeEnv e
          tf = S.recoverExpType typeEnv f
          tg = S.recoverExpType typeEnv g
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c
          d' = convertExp ep d
          e' = convertExp ep e
          f' = convertExp ep f
          g' = convertExp ep g
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc, scalarTypeD td,
               scalarTypeD te, scalarTypeD tf, scalarTypeD tg) of
          (SealedEltTuple (_ :: EltTuple aty),
           SealedEltTuple (_ :: EltTuple bty),
           SealedEltTuple (_ :: EltTuple cty),
           SealedEltTuple (_ :: EltTuple dty),
           SealedEltTuple (_ :: EltTuple ety),
           SealedEltTuple (_ :: EltTuple fty),
           SealedEltTuple (_ :: EltTuple gty)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty,dty,ety,fty,gty))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                      `SnocTup` (downcastE d' :: Exp dty)
                      `SnocTup` (downcastE e' :: Exp ety)
                      `SnocTup` (downcastE f' :: Exp fty)
                      `SnocTup` (downcastE g' :: Exp gty)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty,dty,ety,fty,gty)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple [a,b,c,d,e,f,g,h] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          td = S.recoverExpType typeEnv d
          te = S.recoverExpType typeEnv e
          tf = S.recoverExpType typeEnv f
          tg = S.recoverExpType typeEnv g
          th = S.recoverExpType typeEnv h
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c
          d' = convertExp ep d
          e' = convertExp ep e
          f' = convertExp ep f
          g' = convertExp ep g
          h' = convertExp ep h
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc, scalarTypeD td,
               scalarTypeD te, scalarTypeD tf, scalarTypeD tg, scalarTypeD th) of
          (SealedEltTuple (_ :: EltTuple aty),
           SealedEltTuple (_ :: EltTuple bty),
           SealedEltTuple (_ :: EltTuple cty),
           SealedEltTuple (_ :: EltTuple dty),
           SealedEltTuple (_ :: EltTuple ety),
           SealedEltTuple (_ :: EltTuple fty),
           SealedEltTuple (_ :: EltTuple gty),
           SealedEltTuple (_ :: EltTuple hty)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty,dty,ety,fty,gty,hty))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                      `SnocTup` (downcastE d' :: Exp dty)
                      `SnocTup` (downcastE e' :: Exp ety)
                      `SnocTup` (downcastE f' :: Exp fty)
                      `SnocTup` (downcastE g' :: Exp gty)
                      `SnocTup` (downcastE h' :: Exp hty)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty,dty,ety,fty,gty,hty)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple [a,b,c,d,e,f,g,h,i] ->
      let ta = S.recoverExpType typeEnv a
          tb = S.recoverExpType typeEnv b
          tc = S.recoverExpType typeEnv c
          td = S.recoverExpType typeEnv d
          te = S.recoverExpType typeEnv e
          tf = S.recoverExpType typeEnv f
          tg = S.recoverExpType typeEnv g
          th = S.recoverExpType typeEnv h
          ti = S.recoverExpType typeEnv i
          a' = convertExp ep a
          b' = convertExp ep b
          c' = convertExp ep c
          d' = convertExp ep d
          e' = convertExp ep e
          f' = convertExp ep f
          g' = convertExp ep g
          h' = convertExp ep h
          i' = convertExp ep i
      in case (scalarTypeD ta, scalarTypeD tb, scalarTypeD tc, scalarTypeD td,
               scalarTypeD te, scalarTypeD tf, scalarTypeD tg, scalarTypeD th,
               scalarTypeD ti) of
          (SealedEltTuple (_ :: EltTuple aty),
           SealedEltTuple (_ :: EltTuple bty),
           SealedEltTuple (_ :: EltTuple cty),
           SealedEltTuple (_ :: EltTuple dty),
           SealedEltTuple (_ :: EltTuple ety),
           SealedEltTuple (_ :: EltTuple fty),
           SealedEltTuple (_ :: EltTuple gty),
           SealedEltTuple (_ :: EltTuple hty),
           SealedEltTuple (_ :: EltTuple ity)) ->
            let tup :: Tuple Exp (TupleRepr (aty,bty,cty,dty,ety,fty,gty,hty,ity))
                tup = NilTup
                      `SnocTup` (downcastE a' :: Exp aty)
                      `SnocTup` (downcastE b' :: Exp bty)
                      `SnocTup` (downcastE c' :: Exp cty)
                      `SnocTup` (downcastE d' :: Exp dty)
                      `SnocTup` (downcastE e' :: Exp ety)
                      `SnocTup` (downcastE f' :: Exp fty)
                      `SnocTup` (downcastE g' :: Exp gty)
                      `SnocTup` (downcastE h' :: Exp hty)
                      `SnocTup` (downcastE i' :: Exp ity)
                tup' :: Sm.PreExp acc Exp (aty,bty,cty,dty,ety,fty,gty,hty,ity)
                tup' = Sm.Tuple tup
            in sealExp$ Sm.Exp tup'

    S.ETuple (a:b:c:d:e:f:g:h:i:tl) ->
      error$"convertExp: Alas, tuples greater than size nine are not handled by Accelerate: "++
            show (a:b:c:d:e:f:g:h:i:tl)

    -------------------------------------------------------------------------------
    -- </EXTREME PAIN>

    -- Version 3: try to generalize tuple handling.  Failed, but leave it in a compiling state:
#if 0
    S.ETuple (hd:tl) ->
      let ta = S.recoverExpType typeEnv hd
          tb = S.recoverExpType typeEnv (S.ETuple tl)
          hd' = convertExp ep hd
          tl' = convertExp ep (S.ETuple tl)
      in 
      case (scalarTypeD ta, scalarTypeD tb) of
        (SealedEltTuple (et1 :: EltTuple aty),
         SealedEltTuple (et2 :: EltTuple bty)) ->
          case downcastE tl' :: Exp bty of
            Sm.Exp (Sm.Tuple (tupRst :: Tuple Exp (TupleRepr bty))) ->
             case tupRst of
               (_ :: Tuple Exp brep) ->
                let tup :: Tuple Exp (brep,aty)
                    tup = tupRst `SnocTup` (downcastE hd' :: Exp aty)
--                    tup' :: Sm.PreExp acc Exp (??? bty,aty ???)
--                    tup' = Sm.Tuple tup
                in
                error "FINISHME"    
                -- sealExp$ Sm.Exp tup'
#endif

    {- ========================================================================================== -}
    S.EPrimApp outTy op ls ->
      let args = P.map (convertExp ep) ls 
          (fstArg :_) = ls
          fstArgTy = S.recoverExpType typeEnv fstArg
      in 
      (case scalarTypeD fstArgTy of {
       SealedEltTuple t0 -> 
      (case t0 of {
       PairTuple _ _ -> error$ "Primitive "++show op++" should not have a tuple 1st argument type.";
       UnitTuple     -> error$ "Primitive "++show op++" should not have a unit 1st argument type.";
       SingleTuple (styIn1 :: T.ScalarType eltIn1) ->
      (case scalarTypeD outTy of 
        SealedEltTuple t ->
          case t of
            PairTuple _ _ -> error$ "Primitive "++show op++" should not have a tuple output type."
            UnitTuple     -> error$ "Primitive "++show op++" should not have a unit output type."
            SingleTuple (sty :: T.ScalarType elt) ->

-- <BOILERPLATE abstracted as CPP macros>
-----------------------------------------------------------------------------------              
#define REPBOP(numpat, popdict, which, prim, binop) (numpat, which prim) -> popdict (case args of { \
         [a1,a2] -> let a1',a2' :: Exp elt;    \
                        a1' = downcastE a1;     \
                        a2' = downcastE a2;     \
                    in sealExp (binop a1' a2'); \
         _ -> error$ "Binary operator "++show prim++" expects two args, got "++show args ; })
#define REPUOP(numpat, popdict, which, prim, unop) (numpat, which prim) -> popdict (case args of { \
         [a1] -> let a1' :: Exp elt;     \
                     a1' = downcastE a1;  \
                 in sealExp (unop a1');  \
         _ -> error$ "Unary operator "++show prim++" expects one arg, got "++show args ; })
#define POPINT T.NumScalarType (T.IntegralNumType (nty :: T.IntegralType elt))
#define POPFLT T.NumScalarType (T.FloatingNumType (nty :: T.FloatingType elt))
#define POPIDICT case T.integralDict nty of (T.IntegralDict :: T.IntegralDict elt) ->
#define POPFDICT case T.floatingDict nty of (T.FloatingDict :: T.FloatingDict elt) ->
                                              
-- Monomorphic in second arg:
#define REPBOPMONO(numpat, popdict, which, prim, binop) (numpat, which prim) -> popdict (case args of { \
         [a1,a2] -> let a1' :: Exp elt;         \
                        a1' = downcastE a1;     \
                        a2' :: Exp Int;         \
                        a2' = downcastE a2;     \
                    in sealExp (binop a1' a2'); \
         _ -> error$ "Binary operator "++show prim++" expects two args, got "++show args ; })

#define REPUOP_I2F(prim, unop)  \
      (T.NumScalarType (T.IntegralNumType (ity :: T.IntegralType elt)), FP prim) -> \
        (case T.integralDict ity of { (T.IntegralDict :: T.IntegralDict elt) ->     \
         case styIn1 of { T.NumScalarType (T.FloatingNumType (fty :: T.FloatingType eltF)) -> \
         case T.floatingDict fty of { (T.FloatingDict :: T.FloatingDict eltF) -> \
         case args of { \
          [a1] -> (let a1' :: Exp eltF;    \
                       a1' = downcastE a1; \
                       res :: Exp elt;     \
                       res = unop a1';     \
                   in sealExp res);        \
          _ -> error$ "Unary operator "++show prim++" expects one arg, got "++show args ;};};};})

-----------------------------------------------------------------------------------
             (case (sty,op) of
               REPBOP(POPINT, POPIDICT, NP, Add, (+))
               REPBOP(POPINT, POPIDICT, NP, Sub, (-))
               REPBOP(POPINT, POPIDICT, NP, Mul, (*))
               REPUOP(POPINT, POPIDICT, NP, Abs, abs)
               REPUOP(POPINT, POPIDICT, NP, Neg, (\x -> (-x)))
               REPUOP(POPINT, POPIDICT, NP, Sig, signum)

               REPBOP(POPINT, POPIDICT, IP, Quot, quot)
               REPBOP(POPINT, POPIDICT, IP, Rem,  rem)
               REPBOP(POPINT, POPIDICT, IP, IDiv, div)
               REPBOP(POPINT, POPIDICT, IP, Mod,  mod)
               REPBOP(POPINT, POPIDICT, IP, BAnd, (.&.))
               REPBOP(POPINT, POPIDICT, IP, BOr,  (.|.))
               REPBOP(POPINT, POPIDICT, IP, BXor, xor)
               REPUOP(POPINT, POPIDICT, IP, BNot, complement)
               -- These take monomorphic Int arguments:
               REPBOPMONO(POPINT, POPIDICT, IP, BShiftL, A.shiftL)
               REPBOPMONO(POPINT, POPIDICT, IP, BShiftR, A.shiftR)
               REPBOPMONO(POPINT, POPIDICT, IP, BRotateL, A.rotateL)
               REPBOPMONO(POPINT, POPIDICT, IP, BRotateR, A.rotateR)

               REPBOP(POPFLT, POPFDICT, FP, FDiv, (/))
               REPBOP(POPFLT, POPFDICT, FP, FPow, (**))
               REPBOP(POPFLT, POPFDICT, FP, LogBase, logBase)
               REPBOP(POPFLT, POPFDICT, FP, Atan2, atan2)
               REPUOP(POPFLT, POPFDICT, FP, Recip, recip)
               REPUOP(POPFLT, POPFDICT, FP, Sin, sin)
               REPUOP(POPFLT, POPFDICT, FP, Cos, cos)
               REPUOP(POPFLT, POPFDICT, FP, Tan, tan)
               REPUOP(POPFLT, POPFDICT, FP, Asin, asin)
               REPUOP(POPFLT, POPFDICT, FP, Acos, acos)
               REPUOP(POPFLT, POPFDICT, FP, Atan, atan)
               REPUOP(POPFLT, POPFDICT, FP, Asinh, asinh)
               REPUOP(POPFLT, POPFDICT, FP, Acosh, acosh)
               REPUOP(POPFLT, POPFDICT, FP, Atanh, atanh)
               REPUOP(POPFLT, POPFDICT, FP, ExpFloating, exp)
               REPUOP(POPFLT, POPFDICT, FP, Sqrt, sqrt)
               REPUOP(POPFLT, POPFDICT, FP, Log, log)

               -- Warning!  Heterogeneous input/output types:               
               REPUOP_I2F(Truncate, A.truncate)
               REPUOP_I2F(Round, A.round)
               REPUOP_I2F(Floor, A.floor)
               REPUOP_I2F(Ceiling, A.ceiling)

               -------------- Boolean Primitives --------------
               (_, BP S.And) -> (case args of { 
                 [a1,a2] -> let a1', a2' :: Exp Bool;
                                a1' = downcastE a1;     
                                a2' = downcastE a2;     
                            in sealExp (a1' A.&&* a2'); 
                 _ -> error$ "Boolean AND operator expects two args, got "++show args ; })

               (_, BP S.Or) -> (case args of { 
                 [a1,a2] -> let a1', a2' :: Exp Bool;
                                a1' = downcastE a1;     
                                a2' = downcastE a2;     
                            in sealExp (a1' A.||* a2'); 
                 _ -> error$ "Boolean OR operator expects two args, got "++show args ; })

               (_, BP S.Not) -> (case args of { 
                 [a1] -> let a1' :: Exp Bool;
                             a1' = downcastE a1;
                         in sealExp (A.not a1'); 
                 _ -> error$ "Boolean NOT operator expects one arg, got "++show args ; })


               -------------- Relational/Equality Primitives --------------

-- FINSHME

               -------------- Other Primitives --------------

-- FINSHME

--               _ -> error$ "Primop "++ show op++" expects a scalar type, got "++show outTy
               )
      )  -- End outTy dispatch.
      })}) -- End fstArgTy dispatch.
    -- End PrimApp case.

    S.ELet (vr,ty,rhs) bod ->
      let rhs' = cE rhs
          ep'@(EnvPack _ _ m2) = extendE vr ty rhs' ep
          resTy = scalarTypeD (S.recoverExpType (M.map P.fst m2) bod)
          sty   = scalarTypeD ty
      in
       convertExp ep' bod

    S.ECond e1 e2 e3 ->
      let d1 = cE e1
          d2 = cE e2
          d3 = cE e3
          ty = S.recoverExpType typeEnv e2
      in case scalarTypeD ty of
          SealedEltTuple (t :: EltTuple elt) ->
           -- #define a macro for this?
           case t of
             UnitTuple -> 
               sealExp(((downcastE d1::Exp Bool) A.?
                        (downcastE d2::Exp elt,
                         downcastE d3::Exp elt))::Exp elt)
             SingleTuple _ ->
               sealExp(((downcastE d1::Exp Bool) A.?
                        (downcastE d2::Exp elt,
                         downcastE d3::Exp elt))::Exp elt)
             PairTuple _ _ ->
               sealExp(((downcastE d1::Exp Bool) A.?
                        (downcastE d2::Exp elt,
                         downcastE d3::Exp elt))::Exp elt)


-- | Convert a closed `SimpleAcc` expression (no free vars) into a fully-typed (but
-- sealed) Accelerate one.
convertAcc :: EnvPack -> S.AExp -> SealedAcc
convertAcc env@(EnvPack _ _ mp) ae = 
  case ae of
    S.Vr vr   -> let (_,s) = mp # vr in expectAVar s
    S.Use accarr -> useD accarr
    S.Unit ex ->
      let ex' = convertExp env ex
          ty  = S.recoverExpType (M.map P.fst mp) ex
      in unitD (scalarTypeD ty) ex'
    S.Map (S.Lam1 (vr,ty) bod) inA ->      
      let bodfn ex = convertExp (extendE vr ty ex env) bod
          aty@(TArray dims inty) = P.fst (mp # inA)
          bodty = S.recoverExpType (M.insert vr ty $ M.map P.fst mp) bod
          newAty = arrayTypeD (TArray dims bodty)
          sealedInArr = let (_,sa) = mp # inA in expectAVar sa
      in
        mapD bodfn sealedInArr aty bodty

    S.Fold (S.Lam2 (v1,ty) (v2,ty2) bod) initE inA ->
      trace ("FOLD CASE.. fold of "++show (mp # inA))$
       let init' = convertExp env initE
           bodfn x y = convertExp (extendE v1 ty x$ extendE v2 ty y env) bod
           aty@(TArray dims inty) = P.fst (mp # inA)
           sealedInArr = let (_,sa) = mp # inA in expectAVar sa
       in
        if ty /= ty2 || ty2 /= inty
        then error "Mal-formed Fold.  Input types to Lam2 must match eachother and array input."
        else foldD bodfn init' sealedInArr aty

--    _ -> error$"FINISHME: unhandled: " ++show ae

convertProg :: S.Prog a -> SealedAcc
convertProg S.Prog{progBinds,progResults} =
  error "FINISHME: convertProg"


--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------    

instance Show (EltTuple a) where
  show UnitTuple = "()"
  show (SingleTuple st) = show st
  show (PairTuple a b)  = "("++show a++","++show b++")"

instance Show SealedEltTuple where
  show (SealedEltTuple x) = "Sealed:"++show x

instance Show SealedShapeType where
  show (SealedShapeType (Phantom (_ :: sh))) =
    "Sealed:"++show (toDyn (unused::sh))
    
instance Show SealedArrayType where
  show (SealedArrayType (Phantom (_ :: sh))) =
    "Sealed:"++show (toDyn (unused::sh))


--------------------------------------------------------------------------------
-- Misc, Tests, and Examples
--------------------------------------------------------------------------------  

unused :: a
unused = error "This dummy value should not be used"

-- | For debugging purposes we should really never use Data.Map.!  This is an
-- alternative with a better error message.
(#) :: (Ord a1, Show a, Show a1) => M.Map a1 a -> a1 -> a
mp # k = case M.lookup k mp of
          Nothing -> error$"Map.lookup: key "++show k++" is not in map:\n  "++show mp
          Just x  -> x

c0 :: SealedExp
c0 = constantE (I 99)

c0a :: A.Exp Int
c0a = downcastE c0

{-
-- Small tests:
t0 :: SealedAcc
t0 = convertClosedAExp $
     S.Use (S.AccArray [5,2] (payloadsFromList1$ P.map I [1..10]))
t0b :: Acc (Array DIM2 (Int))
t0b = downcastA t0
-}

t1 = -- convertClosedExp
     convertExp emptyEnvPack 
     (S.ECond (S.EConst (B True)) (S.EConst (I 33)) (S.EConst (I 34)))
t1_ :: A.Exp Int
t1_ = downcastE t1

t2 :: SealedExp
t2 = convertExp emptyEnvPack 
     (S.ELet (v, TInt, (S.EConst (I 33))) (S.EVr v))
 where v = S.var "v" 
t2_ :: Exp Int
t2_ = downcastE t2

t4 = simpleProg
 where
   TestEntry {simpleProg} = allProgsMap # "p1a"

t5 = convertAcc emptyEnvPack (S.Unit (S.EConst (I 33)))
t5_ :: Acc (Scalar Int)
t5_ = downcastA t5


t6 = convertAcc (extendA arr (TArray 0 TInt) t5 emptyEnvPack)
        (S.Map (S.Lam1 (v,TInt) (S.EVr v)) arr)
  where v   = S.var "v"
        arr = S.var "arr"
t6_ :: Acc (Scalar Int)
t6_ = downcastA t6


t7 = convertAcc (extendA arr (TArray 0 TInt) t5 emptyEnvPack)
        (S.Map (S.Lam1 (v,TInt) (S.EPrimApp TInt (S.NP S.Add) [S.EVr v, S.EVr v])) arr)
  where v   = S.var "v"
        arr = S.var "arr"
t7_ :: Acc (Scalar Int)
t7_ = downcastA t7

t8 = convertExp emptyEnvPack (S.ETuple [S.EConst (I 11), S.EConst (F 3.3)])
t8_ :: Exp (Int,Float)
t8_ = downcastE t8


t9 = convertAcc emptyEnvPack $
     S.Use$ S.AccArray [10] [S.ArrayPayloadInt (U.listArray (0,9) [1..10])]
t9_ :: Acc (Vector Int)
t9_ = downcastA t9

t10 = convertAcc (extendA arr (TArray 1 TInt) t9 emptyEnvPack)
        (S.Fold (S.Lam2 (v,TInt) (w,TInt) (S.EPrimApp TInt (S.NP S.Add) [S.EVr v, S.EVr w]))
                (S.EConst (I 0)) arr)
  where v   = S.var "v"
        w   = S.var "w"
        arr = S.var "arr"
t10_ :: Acc (Scalar Int)
t10_ = downcastA t10


p1 = convertExp emptyEnvPack
        (S.EPrimApp TInt (S.NP S.Add) [S.EConst (I 1), S.EConst (I 2)])
p1_ :: Exp Int
p1_ = downcastE p1


p2 = convertExp emptyEnvPack
        (S.EPrimApp TInt (S.NP S.Sig) [S.EConst (I (-11))])
p2_ :: Exp Int
p2_ = downcastE p2

p3 = convertExp emptyEnvPack
        (S.EPrimApp TInt (S.FP Round) [S.EConst (F (9.99))])
p3_ :: Exp Int
p3_ = downcastE p3


c1 :: SealedEltTuple
c1 = scalarTypeD (TTuple [TInt, TInt32, TInt64])

c2 :: SealedEltTuple
c2 = scalarTypeD (TTuple [TTuple [TInt, TInt32], TInt64])
