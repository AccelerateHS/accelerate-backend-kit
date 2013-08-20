{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A library for the runtime construction of fully typed Accelerate programs.

-- IMPORTANT: Tuple representation.
-- We use the same conventions as the TupleRepr type function in Accelerate.
-- We map the untyped tuple constructs onto combinations of pair tuples, i.e.
-- no tuples of arity 3 or higher.  The convention is to nest to the left:
-- 
--    type TupleRepr (a, b, c)  = (TupleRepr (a, b), c)
--
-- 

-- define HACK

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
import           Data.Array.Accelerate.BackendKit.Tests
                    (allProgs, allProgsMap, TestEntry(..), AccProg(..), makeTestEntry, 
                     p1a, p12e, p2c, p2g)
import           Data.Array.Accelerate.BackendKit.SimpleArray (payloadsFromList1)
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter as IS

import Data.Array.Accelerate.Interpreter as I
-- import           Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone (repackAcc)
import           Data.Array.Accelerate.BackendKit.Phase1.ToAccClone (repackAcc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
-- import qualified Data.Array.Accelerate.Array.Data  as Dat

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

----------------------------------------

import qualified Test.HUnit as H
import qualified Test.Framework as TF
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.TH (defaultMainGenerator, testGroupGenerator)

----------------

-- TEMP:
import Data.Array.Accelerate.BackendKit.Phase1.ToAccClone as Cvt (accToAccClone, expToExpClone)
import Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1)
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec))

import qualified Data.Array.Accelerate.Trafo.Sharing as Trafo
import Data.Array.Accelerate.BackendKit.IRs.Internal.AccClone (convertExps)

------------------------------------------------------------------------------------------

-- define DEBUG
#ifdef DEBUG
dbgtrace = trace
#else 
dbgtrace x y = y
#endif

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

sealExp' :: (Elt a, Typeable a) => A.Exp a -> SealedExp
sealExp' exp =
  trace (" !SEALING Exp: "++show exp) (sealExp exp)

sealAcc :: Typeable a => Acc a -> SealedAcc
sealAcc = SealedAcc . toDyn

downcastE :: forall a . Typeable a => SealedExp -> A.Exp a
downcastE (SealedExp d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
      error$"Attempt to unpack SealedExp "++show d
         ++ ", expecting type Exp "++ show (toDyn (unused::a))

downcastA :: forall a . Typeable a => SealedAcc -> Acc a
downcastA (SealedAcc d) =
  case fromDynamic d of
    Just e -> e
    Nothing ->
       error$"Attempt to unpack SealedAcc "++show d
          ++ ", expecting type Acc "++ show (toDyn (unused::a))

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
    Tup ls -> convertExp emptyEnvPack (S.ETuple$ P.map S.EConst ls)
  }

--------------------------------------------------------------------------------
-- Type representations
--------------------------------------------------------------------------------                

-- | We enhance "Data.Array.Accelerate.Type.TupleType" with Elt constraints.
--   This can only construct/represent binary-tree tuples.
data EltTuple a where
  UnitTuple   ::                                               EltTuple ()
  SingleTuple :: (Elt a)        => T.ScalarType a           -> EltTuple a
  PairTuple   :: (Elt a, Elt b) => EltTuple a -> EltTuple b -> EltTuple (a, b)
 deriving Typeable
-- TODO: ^^ Get rid of SingleTuple and possible just use the NilTup/SnocTup rep.


-- | This GADT allows monomorphic value to carry a type inside.
data SealedEltTuple where
  SealedEltTuple :: (Typeable a, Elt a) =>
                    EltTuple a -> SealedEltTuple

-- | This is a bottle in which to store a type that satisfyies the Array class.
data SealedArrayType where
  -- Do we care about the ArrayElt class here?
  SealedArrayType :: (Shape sh, Elt elt, Arrays (Array sh elt)) =>
                     Phantom (Array sh elt) -> SealedArrayType  

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

    -- Here we have a problem... we've lost the surface tuple
    -- representation.... What canonical tuple representation do we use?
    TTuple []      -> SealedEltTuple UnitTuple
    TTuple [sing]  -> scalarTypeD sing -- Allow irregular TTuple.

    -- Here we encode tuple (a..i) as TupleRepr (a..i): a snoclist format.
    TTuple ls ->
      let (lst,rst) = splitLast ls in
      case (scalarTypeD (TTuple rst), scalarTypeD lst) of
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
        UnitTuple                                     -> sealAcc$ unit$ constant ()
        SingleTuple (_ :: T.ScalarType s)             -> sealAcc$ unit (downcastE exp :: A.Exp  s)
        PairTuple (_ :: EltTuple l) (_ :: EltTuple r) -> sealAcc$ unit (downcastE exp :: A.Exp  (l,r))

-- | Dynamically-typed variant of `Data.Array.Accelerate.use`.  However, this version
-- is less powerful, it only takes a single, logical array, not a tuple of arrays.
useD :: S.AccArray -> SealedAcc
useD arr =
  case sty of
    SealedArrayType (Phantom (_ :: (Array sh elt))) ->
      sealAcc$ A.use$
      repackAcc (unused::Acc (Array sh elt)) [arr]
 where
   dty = S.accArrayToType arr
   sty = arrayTypeD dty

generateD :: SealedExp -> (SealedExp -> SealedExp) ->
        S.Type -> SealedAcc 
generateD indSealed bodfn outArrTy =
  dbgtrace (" ** starting generateD fun: outArrTy "++show (outArrTy)) $
      let (TArray dims outty) = outArrTy in
       case (shapeTypeD dims, scalarTypeD outty) of
         (SealedShapeType (_ :: Phantom shp), 
          SealedEltTuple (outET :: EltTuple outT)) ->           
          let
            rawfn :: Exp shp -> Exp outT
            rawfn x =
              dbgtrace (" **   Inside generate scalar fun, downcasting bod "++
                     show (bodfn (sealExp x))++" to "++ show (typeOf (undefined::outT))) $
              downcastE (bodfn (sealExp x))
            dimE :: Exp shp
            dimE = dbgtrace (" **   Generate: downcasting dim "++show indSealed++
                             " Expecting Z-based index of dims "++show dims
                             ++", type "++ show(typeOf(undefined::shp))) $
                   downcastE indSealed
            acc = A.generate dimE rawfn
          in
           dbgtrace (" **   .. Body of generateD: raw acc: "++show acc) $
           sealAcc acc


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
 deriving Show

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

-- | Reseal as a real Acceelerate tuple, but still use the internal
-- tuple representation.  This function takes tuple components in the
-- same order as ETuple.
resealTup :: [(SealedEltTuple, SealedExp)] -> (SealedEltTuple,SealedExp)
resealTup [] = (SealedEltTuple UnitTuple, sealExp$ A.constant ())
resealTup [one] = one

resealTup (et1@(SealedEltTuple (et1' :: EltTuple aty), a') : rst) =
    let (et2,rst') = resealTup rst in
    case et2 of
      SealedEltTuple (et2' :: EltTuple rstTy) -> 
       (SealedEltTuple (PairTuple et2' et1'),
        sealExp$ Sm.tup2 (downcastE rst' :: Exp rstTy,
                          downcastE a'   :: Exp aty))

-- resealTup [(SealedEltTuple (_ :: EltTuple aty), a'),
--            (SealedEltTuple (_ :: EltTuple bty), b')] =
--     sealExp$ Sm.tup2 (downcastE a' :: Exp bty,
--                       downcastE b' :: Exp aty)
-- resealTup [(SealedEltTuple (_ :: EltTuple aty), a),
--            (SealedEltTuple (_ :: EltTuple bty), b),
--            (SealedEltTuple (_ :: EltTuple cty), c)] =
--     let tup1 = Sm.tup2 (downcastE a :: Exp aty, downcastE b :: Exp bty)
--         tup2 = Sm.tup2 (tup1, downcastE c :: Exp cty)
--     in sealExp tup2
-- resealTup components =  
--   error$ "resealTup: mismatched or unhandled tuple: "++show components

-- | Convert an entire `SimpleAcc` expression into a fully-typed (but sealed) Accelerate one.
--   Requires a type environments for the (open) `SimpleAcc` expression:    
--   one for free expression variables, one for free array variables.
--     
convertExp :: EnvPack -> S.Exp -> SealedExp
convertExp ep@(EnvPack envE envA mp) ex =
  dbgtrace(" @ Converting exp "++show ex++" with env "++show (M.map P.snd mp)) $
  dbgtrace(" @-> converted exp, result: "++show result) $
  result
 where 
  cE = convertExp ep
  typeEnv  = M.map P.fst mp -- Strip out the SealedExp/Acc bits leaving just the types.
  resultTy = S.recoverExpType typeEnv ex
  result =  
   case ex of
    S.EConst c -> constantE c

    -- This is tricky, because it needs to become a deBruin index ultimately...
    -- Or we need to stay at the level of HOAS...
    S.EVr vr -> let (_,se) = mp # vr in expectEVar se

    S.EShape _          -> error "FINISHME: convertExp needs to handle EShape"
    S.EShapeSize ex     ->
      let ty = S.recoverExpType typeEnv ex
          tup = convertExp ep ex in
      
      (error "FINISHME: convertExp needs to handle EShapeSize")
      
    S.EIndex _          -> error "FINISHME: convertExp needs to handle EIndex"
    S.EIndexScalar vr indEx ->
      let (aty,s) = mp # vr
          sa = expectAVar s
          tupTy = S.recoverExpType typeEnv indEx
      in
       case arrayTypeD aty of
         SealedArrayType (_ :: Phantom (Array sh elt)) ->
           let indEx' = tupToIndex tupTy $ convertExp ep indEx
               res :: Exp elt
               res = (A.!) (downcastA sa :: Acc (Array sh elt))
                           (downcastE indEx' :: Exp sh) in 
           sealExp res

    -- This is tricky because we are projecting a slice from the
    -- in-order traversal of a binary-tree of tuples.

    S.ETupProject {S.projlen=0} -> error "convertE: ETupProject of zero length!"

    -- TEMPORARY: for now we assume the input tuples have been
    -- FLATTENED.  That means that we end up with a left-nested
    -- snoc-tuple tree, not an arbitrary binary tree.
    S.ETupProject {S.indexFromRight=origind, S.projlen=len, S.tupexpr=tex} ->
      let                  
          -- Scan to the point where we begin the slice:
          loop1 0 et tup = loop2 len et tup []
          loop1 ind (SealedEltTuple et1) tup =
           case et1 of
             UnitTuple -> notEnough
             SingleTuple (_ :: T.ScalarType s) -> notEnough 
             PairTuple (etA :: EltTuple aa) (_ :: EltTuple bb) ->
               let a :: Exp aa;  b :: Exp bb; 
                   (a,b) = unlift (downcastE tup :: Exp (aa,bb))
               in loop1 (ind-1) (SealedEltTuple etA) (sealExp a)
          loop2 0 _ _ !acc = P.snd$ resealTup acc
          loop2 remain (SealedEltTuple et1) tup !acc =
            case et1 of
             UnitTuple -> notEnough
             SingleTuple (_ :: T.ScalarType s) ->
               if remain == 1
               then P.snd$ resealTup ((SealedEltTuple et1,tup) : acc)
               else notEnough
             PairTuple (etA :: EltTuple aa) (etB :: EltTuple bb) ->
               let a :: Exp aa;  b :: Exp bb;
                   (a,b) = unlift (downcastE tup :: Exp (aa,bb))
               in loop2 (remain-1) (SealedEltTuple etA) (sealExp a)
                        ((SealedEltTuple etB, sealExp b) : acc)
          notEnough = error$ "convertExp/ETupProject: not enough elements: "++show ex
          tty  = S.recoverExpType typeEnv tex
          origtup = convertExp ep tex      
      in loop1 origind (scalarTypeD tty) origtup
       
    S.ETuple []    -> constantE (Tup [])
    S.ETuple [ex]  -> convertExp ep ex

    -- ETuple is a flattened N-tuple representation.
    -- This is converted directly into a nested/pair-based TupleRepr.
    --   type TupleRepr (a, b, c)  = (TupleRepr (a, b), c)
    S.ETuple ls ->
      let
          (hd,tl) = splitLast ls
          thd = S.recoverExpType typeEnv hd
          ttl = S.recoverExpType typeEnv tltup
          hd' = convertExp ep hd
          tl' = convertExp ep tltup
          tltup = if P.null (P.tail tl) 
                  then head tl else S.ETuple tl
      in 
      case (scalarTypeD thd, scalarTypeD ttl) of
        (SealedEltTuple (et1 :: EltTuple hdty),
         SealedEltTuple (et2 :: EltTuple tlty)) ->
          sealExp$ Sm.tup2 (downcastE tl' :: Exp tlty,
                            downcastE hd' :: Exp hdty)

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
            SingleTuple (styOut :: T.ScalarType elt) ->

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
             (case (styOut,op) of
               REPBOP(POPINT, POPIDICT, NP, Add, (+))
               REPBOP(POPINT, POPIDICT, NP, Sub, (-))
               REPBOP(POPINT, POPIDICT, NP, Mul, (*))
               REPUOP(POPINT, POPIDICT, NP, Abs, abs)
               REPUOP(POPINT, POPIDICT, NP, Neg, (\x -> (-x)))
               REPUOP(POPINT, POPIDICT, NP, Sig, signum)
               -- UGH, do the same thing with float dicts:
               REPBOP(POPFLT, POPFDICT, NP, Add, (+))
               REPBOP(POPFLT, POPFDICT, NP, Sub, (-))
               REPBOP(POPFLT, POPFDICT, NP, Mul, (*))
               REPUOP(POPFLT, POPFDICT, NP, Abs, abs)
               REPUOP(POPFLT, POPFDICT, NP, Neg, (\x -> (-x)))
               REPUOP(POPFLT, POPFDICT, NP, Sig, signum)

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

               -------------- Other Primitives --------------

               -- FromIntegral case 1/2: integral->integral
               (T.NumScalarType (T.IntegralNumType (ityOut :: T.IntegralType elt)), 
                OP S.FromIntegral) -> 
                (case T.integralDict ityOut of { (T.IntegralDict :: T.IntegralDict elt) -> 
                 case styIn1 of { T.NumScalarType (T.IntegralNumType (ity :: T.IntegralType inElt)) ->
                 case T.integralDict ity of { (T.IntegralDict :: T.IntegralDict inElt) -> 
                 case args of {
                 [a1] -> let a1' :: Exp inElt;
                             a1' = downcastE a1;
                             res :: Exp elt
                             res = A.fromIntegral a1'
                         in sealExp res;
                 _ -> error$ "fromIntegral operator expects one arg, got "++show args ;};};};})

               -- FromIntegral case 2/2: integral->floating
               (T.NumScalarType (T.FloatingNumType (ityOut :: T.FloatingType elt)), 
                OP S.FromIntegral) -> 
                (case T.floatingDict ityOut of { (T.FloatingDict :: T.FloatingDict eltF) -> 
                 case styIn1 of { T.NumScalarType (T.IntegralNumType (ity :: T.IntegralType inElt)) ->
                 case T.integralDict ity of { (T.IntegralDict :: T.IntegralDict inElt) -> 
                 case args of {
                 [a1] -> let a1' :: Exp inElt;
                             a1' = downcastE a1;
                             res :: Exp elt
                             res = A.fromIntegral a1'
                         in sealExp res;
                 _ -> error$ "fromIntegral operator expects one arg, got "++show args ;};};};})

-- FINSHME
               --------------------------------------------------
               _ -> error$ "Primop unhandled or got wrong argument type: "++show op++" / "++show outTy
               )
      )  -- End outTy dispatch.
      })}) -- End fstArgTy dispatch.
    -- End PrimApp case.

    S.ELet (vr,ty,rhs) bod ->
      let rhs' = cE rhs
          ep'@(EnvPack _ _ m2) = extendE vr ty rhs' ep
          resTy = scalarTypeD (S.recoverExpType (M.map P.fst m2) bod)
      in
       convertExp ep' bod

-- Reduce repetition when all you need is to peek inside a single sealed EltTuple to retrieve instances:
#define POP_SELTUPLE(et, bod) case et of { SealedEltTuple (tt :: EltTuple elt) -> \
                              case tt of { UnitTuple -> bod; \
                                           SingleTuple _ -> bod; \
                                           PairTuple _ _ -> bod; }; }
    S.ECond e1 e2 e3 ->
      let d1 = cE e1
          d2 = cE e2
          d3 = cE e3
          ty = S.recoverExpType typeEnv e2
      in 
      POP_SELTUPLE(scalarTypeD ty, 
                   sealExp(((downcastE d1::Exp Bool) A.?
                            (downcastE d2::Exp elt,
                             downcastE d3::Exp elt))::Exp elt))


-- | The SimpleAcc representation does NOT keep index types disjoint
-- from regular tuples.  To convert back to Acc we need to reassert
-- this distinction, which involves "casting" indices to tuples and
-- tuples to indices at the appropriate places.
indexToTup :: S.Type -> SealedExp -> SealedExp
indexToTup ty ex =
  dbgtrace (" -- starting indexToTup... ")$ 
  dbgtrace (" -- indexTo tup, converted "++show (ty,ex)++" to "++ show res)
   res
  where
    res = 
     case ty of
       TTuple [] -> sealExp (constant ())

       TTuple [TInt,TInt] -> 
         let a,b :: Exp Int
             (Z :. a :. b) = unlift (downcastE ex :: Exp (Z :. Int :. Int))
             tup :: Exp (Int, Int)
             tup = lift (a, b)
         in sealExp tup

       TTuple [TInt,TInt,TInt] -> 
         let a,b,c :: Exp Int
             (Z :. a :. b :. c) = unlift (downcastE ex :: Exp (Z :. Int :. Int :. Int))
             tup :: Exp ((Int, Int),Int)
             tup = lift ((a,b),c)
         in sealExp tup

-- FINISHME: Go up to tuple size 9.

       TTuple ls -> error$ "indexToTup: tuple type not handled: "++show(ty,ex)
       TArray{}  -> error$ "indexToTup: expected tuple-of-scalar type, got: "++show ty
       _ ->
         case scalarTypeD ty of      
           SealedEltTuple (t :: EltTuple elt) ->
             let
                 z :: Exp (Z :. elt)
                 z = downcastE ex
                 e' :: Exp (elt)
                 Z :. e' = unlift z
             in sealExp e'

liftScons :: (Slice a, Elt b) => 
             Exp a -> Exp b -> Exp (a :. b)
liftScons a b = lift (a :. b)

-- | The inverse of `indexToTup`
tupToIndex :: S.Type -> SealedExp -> SealedExp
tupToIndex ty ex0 =
    dbgtrace (" ~~ starting tupToIndex... ")$ 
    dbgtrace (" ~~ tupToIndex tup, converted "++show (ty,ex0)++" to "++ show res) res
 where
 res =  
  case ty of
    TTuple []  -> sealExp (constant Z)
    TInt -> 
      dbgtrace (" ~~   Converting TInt to index type... "++show ty) $
          let a :: Exp Int
              a = downcastE ex0
              ind' :: Exp (Z :. Int)
              ind' = lift (Z :. a)
          in sealExp ind'
    
#if 0     
    TTuple [a] -> error$ "tupToIndex: internal error, singleton tuple: "++show (ty,ex0)

    TTuple [TInt,TInt] -> 
      dbgtrace (" ~~   Converting pair tuple type to index type... "++show ty) $
          let a,b :: Exp Int
              (a,b) = unlift (downcastE ex0 :: Exp (Int,Int))
              ind' :: Exp (Z :. Int :. Int)
              ind' = lift (Z :. a :. b)
          in sealExp ind'

    TTuple [TInt,TInt,TInt] -> 
      dbgtrace (" ~~  Converting triplet tuple type to index type... "++show ty) $
          -- On the Acc side we're ONLY using pairs:
          let a,b,c :: Exp Int
              ab :: Exp (Int,Int)
              (ab,c) = unlift (downcastE ex0 :: Exp ((Int,Int),Int))
              (a,b) = unlift ab
              ind' :: Exp (Z :. Int :. Int :. Int)
              ind' = lift (Z :. a :. b :. c)
          in sealExp ind'
#else
    -- TTuple [TTuple [], TInt] -> 
    --   dbgtrace (" ~~   Converting SINGLETON (!?) tuple type to index type... "++show ty) $
    --       let a :: Exp Int
    --           unt :: Exp ()
    --           (unt,a) = unlift (downcastE ex0 :: Exp ((),Int))
    --           ind' :: Exp (Z :. Int)
    --           ind' = lift (Z :. a)
    --       in sealExp ind'

    TTuple [TTuple [TTuple [], TInt],TInt] -> 
      dbgtrace (" ~~   Converting pair tuple type to index type... "++show ty) $
          let a,b :: Exp Int
              (a,b) = unlift (downcastE ex0 :: Exp (Int,Int))
              ind' :: Exp (Z :. Int :. Int)
              ind' = lift (Z :. a :. b)
          in sealExp ind'

    TTuple [TTuple [TTuple [TTuple [],TInt],TInt],TInt] -> 
      dbgtrace (" ~~  Converting triplet tuple type to index type... "++show ty) $
          -- On the Acc side we're ONLY using pairs:
          let a,b,c :: Exp Int
              ab :: Exp (Int,Int)
              (ab,c) = unlift (downcastE ex0 :: Exp ((Int,Int),Int))
              (a,b) = unlift ab
              ind' :: Exp (Z :. Int :. Int :. Int)
              ind' = lift (Z :. a :. b :. c)
          in sealExp ind'
#endif


 -- PROBLEM: Doing this in general requires knowing (Slice rstElt):
 -- We could conceivable do something like SealedEltTuple that stores the Slice instance...
    TTuple ls@(hd:tl) | P.all (TInt ==) ls -> 
      dbgtrace ("Converting tuple type to index type... "++show ty) $
       case scalarTypeD (TTuple tl) of
          SealedEltTuple (_ :: EltTuple rstElt) ->
           -- On the Acc side we're ONLY using pairs:
           let a :: Exp Int
               b :: Exp rstElt
               (a,b) = unlift (downcastE ex0 :: Exp (Int,rstElt))
--              ind  :: Exp rstElt
--              ind   = tupToIndex (TTuple tl) (sealExp b)
--               ind' :: Exp (rstElt :. Int)
-- PROBLEMS:
--               ind'  = lift (ind :. a)
--               ind'  = lift (b :. a)
           in error "FINISHME: tupToIndex recursive case" -- sealExp ind'
      
-- FINISHME: Go up to tuple size 9.

    TTuple _ -> error$"tupToIndex: unhandled tuple type: "++ show ty

    TArray{}  -> error$ "tupToIndex: expected tuple-of-scalar type, got: "++show ty
    _ -> 
      case scalarTypeD ty of      
        SealedEltTuple (t :: EltTuple elt) ->
          let
              z :: Z :. Exp elt
              z = Z :. ((downcastE ex0) :: Exp elt)
              z' :: Exp (Z :. elt)
              z' = lift z
          in sealExp z'

tupTyLen (TTuple ls) = length ls
tupTyLen _           = 1

-- | Convert a closed `SimpleAcc` expression (no free vars) into a fully-typed (but
-- sealed) Accelerate one.
convertAcc :: EnvPack -> S.AExp -> SealedAcc
convertAcc env@(EnvPack _ _ mp) ae =
  let typeEnv = M.map P.fst mp in
  case ae of
    S.Vr vr   -> let (_,s) = mp # vr in expectAVar s
    S.Use accarr -> useD accarr
    S.Unit ex ->
      let ex' = convertExp env ex
          ty  = S.recoverExpType (M.map P.fst mp) ex
      in unitD (scalarTypeD ty) ex'

    S.Generate initE (S.Lam1 (vr,ty) bod) ->
      let -- Expose the index coming in as a plain tuple:
          bodfn ex  = let env'@(EnvPack _ _ m2) = extendE vr ty (indexToTup ty ex) env in
                      dbgtrace ("Generate/bodyfun called: extended environment to: "++show (M.map P.snd m2))$
                      convertExp env' bod
          bodty     = S.recoverExpType (M.insert vr ty typeEnv) bod
          -- TODO: Replace this by simply passing in the result type to convertAcc:
          dims = tupTyLen$ S.recoverExpType typeEnv initE 
          outArrTy  = TArray dims bodty
          init' = tupToIndex ty$ convertExp env initE 
      in
       dbgtrace ("Generate: computed body type: "++show bodty) $ 
       generateD init' bodfn outArrTy
         
    S.Map (S.Lam1 (vr,ty) bod) inA -> 
      let bodfn ex = convertExp (extendE vr ty ex env) bod
          aty@(TArray dims inty) = P.fst (mp # inA)
          bodty = S.recoverExpType (M.insert vr ty $ M.map P.fst mp) bod
          newAty = arrayTypeD (TArray dims bodty)
          sealedInArr = let (_,sa) = mp # inA in expectAVar sa
      in
        mapD bodfn sealedInArr aty bodty

    S.Fold (S.Lam2 (v1,ty) (v2,ty2) bod) initE inA ->
      dbgtrace ("FOLD CASE.. fold of "++show (mp # inA))$
       let init' = convertExp env initE
           bodfn x y = convertExp (extendE v1 ty x$ extendE v2 ty y env) bod
           aty@(TArray dims inty) = P.fst (mp # inA)
           sealedInArr = let (_,sa) = mp # inA in expectAVar sa
       in
        if ty /= ty2 || ty2 /= inty
        then error "Mal-formed Fold.  Input types to Lam2 must match eachother and array input."
        else foldD bodfn init' sealedInArr aty

    _ -> error$"FINISHME: convertAcc: unhandled array operation: " ++show ae

convertProg :: S.Prog () -> SealedAcc
convertProg S.Prog{progBinds,progResults} =
    doBinds emptyEnvPack progBinds
  where 
  doBinds env (S.ProgBind vr ty dec eith : rst) =
    dbgtrace (" dobinds of "++show (vr,ty,rst)++" "++show env) $ 
    case eith of
      Left ex  -> let se = convertExp env ex
                      env' = extendE vr ty se env
                  in doBinds env' rst
      Right ae -> let sa = convertAcc env ae
                      env' = extendA vr ty sa env
                  in doBinds env' rst
  doBinds (EnvPack _ _ mp) [] =
    case S.resultNames progResults of
      [resVr] -> expectAVar$ P.snd$ mp # resVr
      _ -> error$ "FINISHME: convertProg with multiple results: "++show progResults
  


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
  show (SealedArrayType (Phantom (_ :: Array sh elt))) =
    "Sealed:"++show (toDyn (unused :: Array sh elt))


--------------------------------------------------------------------------------
-- Misc Helpers
--------------------------------------------------------------------------------
  
splitLast []                 =  error "splitLast: cannot take empty list"
splitLast (x:xs)             =  go x xs
  where go lst []   = (lst,[])
        go y (z:zs) =
          let (lst,zs') = go z zs in
          (lst, y:zs')

unused :: a
unused = error "This dummy value should not be used"

-- | For debugging purposes we should really never use Data.Map.!  This is an
-- alternative with a better error message.
(#) :: (Ord a1, Show a, Show a1) => M.Map a1 a -> a1 -> a
mp # k = case M.lookup k mp of
          Nothing -> error$"Map.lookup: key "++show k++" is not in map:\n  "++show mp
          Just x  -> x

--------------------------------------------------------------------------------
-- Tests, and Examples
--------------------------------------------------------------------------------

t1 = -- convertClosedExp
     convertExp emptyEnvPack 
     (S.ECond (S.EConst (B True)) (S.EConst (I 33)) (S.EConst (I 34)))
t1_ :: A.Exp Int
t1_ = downcastE t1
case_if = H.assertEqual "if and const" (show t1_) "33"

t2 :: SealedExp
t2 = convertExp emptyEnvPack 
     (S.ELet (v, TInt, (S.EConst (I 33))) (S.EVr v))
 where v = S.var "v" 
t2_ :: Exp Int
t2_ = downcastE t2
case_const = H.assertEqual "simple const" (show t2_) "33"

t3 = makeTestEntry "t3" (A.unit (constant (3::Int,4::Int64)))
t3_ = roundTrip t3
case_tup = t3_
-- case_tup = H.assertEqual "tup const" "" (show$ I.run )

-- | The same as t3 but with a different way to form the tuple:
t3B = makeTestEntry "t3B" (A.unit ((lift (constant (3::Int),constant (4::Int64))) :: Exp (Int,Int64)))
t3B_ = roundTrip t3B
case_tupB = t3B_

-- | This one actually returns an array index.  The problem is, from
-- the SimpleAcc converted representation, there's no way to tell that
-- an index should be returned rather than a plain tuple.
t4 = makeTestEntry "t4" (A.unit (constant (Z :. (3::Int) :. (4::Int))))
t4_ = roundTrip t4
case_tupInd = t4_

itt :: Exp (Int,Int)
itt = downcastE$ indexToTup (TTuple [TInt,TInt]) (sealExp$ constant (Z :. (3::Int) :. (4::Int)))
case_indToTup = H.assertEqual "indexToTup" "Array (Z) [(3,4)]" (show$ I.run$ A.unit itt)

tti :: Exp (Z :. Int :. Int)
tti = downcastE$ tupToIndex (TTuple [TInt,TInt]) (sealExp$ constant (3::Int, 4::Int))
case_tupToInd = H.assertEqual "tupToIndex" "Array (Z) [(Z :. 3) :. 4]" (show$ I.run$ A.unit tti)



t5 = convertAcc emptyEnvPack (S.Unit (S.EConst (I 33)))
t5_ :: Acc (Scalar Int)
t5_ = downcastA t5
case_unit = H.assertEqual "unit array" (show$ I.run t5_) "Array (Z) [33]"

t6 = convertAcc (extendA arr (TArray 0 TInt) t5 emptyEnvPack)
        (S.Map (S.Lam1 (v,TInt) (S.EVr v)) arr)
  where v   = S.var "v"
        arr = S.var "arr"
t6_ :: Acc (Scalar Int)
t6_ = downcastA t6
case_mapId = H.assertEqual "map id function" (show$ I.run t6_) "Array (Z) [33]"


t7 = convertAcc (extendA arr (TArray 0 TInt) t5 emptyEnvPack)
        (S.Map (S.Lam1 (v,TInt) (S.EPrimApp TInt (S.NP S.Add) [S.EVr v, S.EVr v])) arr)
  where v   = S.var "v"
        arr = S.var "arr"
t7_ :: Acc (Scalar Int)
t7_ = downcastA t7
case_mapAdd = H.assertEqual "map add fun" (show$ I.run t7_) "Array (Z) [66]"

t8 = convertExp emptyEnvPack (S.ETuple [S.EConst (I 11), S.EConst (F 3.3)])
t8_ :: Exp (Int,Float)
t8_ = downcastE t8
case_pairExp = H.assertEqual "simple pair"
             (show $ I.run$ A.unit t8_)
--             (A.fromList Z [(11,3.3)]) -- Why is there no EQ for Accelerate arrays?
             "Array (Z) [(11,3.3)]"

t9 = convertAcc emptyEnvPack $
     S.Use$ S.AccArray [10] [S.ArrayPayloadInt (U.listArray (0,9) [1..10])]
t9_ :: Acc (Vector Int)
t9_ = downcastA t9
case_use = H.assertEqual "use array" (show $ I.run$ t9_)
           "Array (Z :. 10) [1,2,3,4,5,6,7,8,9,10]"

t10 = convertAcc emptyEnvPack $
      S.Generate (S.EConst (I 10)) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v,TInt) (S.EVr v))
  where v   = S.var "v"
t10_ :: Acc (Vector Int)
t10_ = downcastA t10
case_generate1 = H.assertEqual "generate1" (show $ I.run$ t10_)
                 "Array (Z :. 10) [0,1,2,3,4,5,6,7,8,9]"

t11 = convertAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2)]) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v, TTuple [TInt,TInt]) (S.EVr v))
  where v   = S.var "v"
t11_ :: Acc (Array DIM2 (Int,Int))
t11_ = downcastA t11
case_generate2D = H.assertEqual "generate2" (show $ I.run$ t11_)
                 "Array (Z :. 3 :. 2) [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]"

-- | This test exercises only tuples on the input side, plus tuple field projection.
t12 = convertAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2)]) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v, TTuple [TInt,TInt]) (S.ETupProject 1 1 (S.EVr v)))
  where v   = S.var "v"
t12_ :: Acc (Array DIM2 Int)
t12_ = downcastA t12
case_generatePrj = H.assertEqual "generate3"
                   (show$ I.run$ t12_)
                   (show$ I.run ref12)
--                   "Array (Z :. 3 :. 2) [0,0,1,1,2,2]"
-- Manually translated version:
ref12 = A.generate (constant (Z :. (3::Int) :. (2 :: Int)))
                  (\x0 -> indexHead (indexTail x0))

v = S.var "v"
avr = S.var "arr"

-- | Now project TWO components out of THREE.
t13 = convertAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2), S.EConst (I 1)]) -- (S.EIndex [S.EConst (I 10)])
                 (S.Lam1 (v, TTuple [TInt,TInt,TInt])
                    (S.ETupProject 1 2 (S.EVr v)))
t13_ :: Acc (Array DIM3 (Int,Int))
t13_ = downcastA t13
case_generatePrj2 = H.assertEqual "generate4"
                   (show$ I.run$ t13_)
                   -- "Array (Z :. 3 :. 2 :. 1) [(0,0),(1,0),(0,0),(1,0),(0,0),(1,0)]"
                   (show$ I.run ref13)

-- This is the program that matches t13_.  Whether that is correct we should audit.
ref13 = A.generate (constant (Z :. (3::Int) :. (2 :: Int) :. (1 :: Int)))
          (\x -> let a,b,c :: Exp Int
                     (Z :. a :. b :. c) = unlift x
                 in lift (a,b))

t14 = convertAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2), S.EConst (I 1)]) 
                 (S.Lam1 (v, TTuple [TInt,TInt,TInt]) (S.EVr v))
t14_ :: Acc (Array DIM3 ((Int,Int),Int))
t14_ = downcastA t14
case_t14_generate = H.assertEqual "generate5"
                   (show$ I.run$ ref14)
                   (show$ I.run$ t14_)

ref14 = A.generate (constant (Z :. (3::Int) :. (2 :: Int) :. (1 :: Int)))
          (\x -> let a,b,c :: Exp Int
                     (Z :. a :. b :. c) = unlift x
                 in lift ((a,b),c))

i15 = convertAcc emptyEnvPack $
      S.Generate (S.ETuple [S.EConst (I 3), S.EConst (I 2), S.EConst (I 1)]) 
                 (S.Lam1 (v, TTuple [TInt,TInt,TInt])
                  (S.ETuple [ S.ETuple [(S.ETupProject 0 1 (S.EVr v)),
                                       (S.ETupProject 1 1 (S.EVr v))],
                             (S.ETupProject 2 1 (S.EVr v)) ])
                 )

i15_ :: Acc (Array DIM3 ((Int,Int),Int))
i15_ = downcastA i15
case_generateTupLeftNest = H.assertEqual "generate6"
                           (show$ I.run$ i15_)
                           "Array (Z :. 3 :. 2 :. 1) [((0,0),0),((0,1),0),((0,0),1),((0,1),1),((0,0),2),((0,1),2)]"

t16 :: SealedExp
t16 = convertExp (extendA avr (TArray 0 TInt) t5 emptyEnvPack)
                 (S.EIndexScalar avr nullInd)
t16_ :: Exp Int
t16_ = downcastE t16
case_indexScalar = H.assertEqual "EIndexScalar" (show$ I.run (A.unit t16_)) "Array (Z) [33]"

nullInd :: S.Exp
nullInd = convertExps $
          expToExpClone  (Trafo.convertExp True (constant Z))

--------------------------------------------------
-- Test PrimApps:

p1 = convertExp emptyEnvPack
        (S.EPrimApp TInt (S.NP S.Add) [S.EConst (I 1), S.EConst (I 2)])
p1_ :: Exp Int
p1_ = downcastE p1

case_primApp_Add = H.assertEqual "primapp_add" (show p1_) "3"

p2 = convertExp emptyEnvPack
        (S.EPrimApp TInt (S.NP S.Sig) [S.EConst (I (-11))])
p2_ :: Exp Int
p2_ = downcastE p2
case_primApp_Sig = H.assertEqual "primapp_sig" (show p2_) "-1"

p3 = convertExp emptyEnvPack
        (S.EPrimApp TInt (S.FP Round) [S.EConst (F (9.99))])
p3_ :: Exp Int
p3_ = downcastE p3
case_primApp_Round = H.assertEqual "primapp_sig" (show p3_) "10"

--------------------------------------------------
-- Test Constant conversion

c0 :: SealedExp
c0 = constantE (I 99)
c0_ :: A.Exp Int
c0_ = downcastE c0

c1 :: SealedEltTuple
c1 = scalarTypeD (TTuple [TInt, TInt32, TInt64])

c2 :: SealedEltTuple
c2 = scalarTypeD (TTuple [TTuple [TInt, TInt32], TInt64])

case_const0 = H.assertEqual "int const" (show c0_) "99"

-- For now we are NOT recovering tuple structure for tuple size > 3.
case_const1 = H.assertEqual "tuple repr 1"
            (show c1)  "Sealed:((Int,Int32),Int64)"
            
case_const2 = H.assertEqual "tuple repr 2"
            (show c2) "Sealed:((Int,Int32),Int64)"


--------------------------------------------------
-- Complete program unit tests

allProg_tests = TF.testGroup "Backend kit unit tests" $
                [ testCase ("progtest_"++name te) (roundTrip te)
                | te <- allProgs ]

-- Note, most don't work yet, as expecte,d [2013.08.14] but check out
-- p12e, which seems to indicate a bug.

bug2 :: Acc (Scalar Int)
bug2 = unit $
  let tup :: Exp (Int,Int64)
      tup   = constant True ? (lift (11::Int, 22::Int64),
                               lift (100::Int, 200::Int64))
      (a,b) = unlift tup :: (Exp Int, Exp Int64)
  in a + 33

bug2_ :: Acc (Scalar Int)
bug2_ = downcastA $ convertProg$ phase1$ phase0 bug2

-- Current problems: p2c, p2g

bug :: Acc (Array DIM2 (Int,Int))
bug = downcastA (convertProg$ phase1$ phase0 p2g')

-- | Similar to p2c, except now simply return indices:
p2g' :: Acc (Array DIM2 (Int,Int))
p2g' = generate (constant (Z :. (3::Int) :. (2::Int))) unindex2

-- | The trickiness here is that we convert a program to its tuple-converted "Repr".
-- 
--   But there's no available type-level function for surface->repr of
--   at BOTH the array level and the Elt level, that is, a combination of toArr and toTuple.
roundTrip :: TestEntry -> IO ()
roundTrip TestEntry{name, simpleProg, origProg= AccProg (acc :: Acc aty) } = do
  -- This is a bit odd because we RUN it in its internal "Repr" mode:
  let
#if 0
      ar0 :: Acc (Sug.ArrReprDeep aty)
      ar0 = downcastA $ convertProg simpleProg
      ar1 :: Sug.ArrReprDeep aty
      ar1 = I.run ar0
      ar2 :: aty
      ar2 = Sug.toArr ar1
      res = ar2
#else
      ar0 :: Acc aty
      ar0 = downcastA $ convertProg simpleProg
      res = I.run ar0
#endif
  dbgtrace ("RoundTripping:\n" ++ show acc) $ 
   H.assertEqual ("roundTrip "++name)
                 (show$ I.run acc)
                 (show res)

--------------------------------------------------
-- Aggregate tests:

runTests = TF.defaultMain [unitTests]

unitTests =
  TF.testGroup "AllTests" [
    $(testGroupGenerator),
    allProg_tests
  ]


    
