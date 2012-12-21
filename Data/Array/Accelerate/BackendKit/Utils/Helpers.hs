{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

{- | This module contains helpers that are specific to the
     "Vectorized CodeGen" class using Accelerate.

     Thus this module depends on "Data.Array.Accelerate.SimpleAST".
     It also depends on EasyEmit.
-}

module Data.Array.Accelerate.BackendKit.Utils.Helpers
       ( 
         -- * Some help with code-emission:
         emitPrimApp, emitCType, emitOpenCLType, 
         
         -- * Helpers that capture certain conventions that the compiler follows:
         builderName, shapeName, strideName, mkIndTy, isTupleTy,
         GensymM, genUnique, genUniqueWith,
         
         -- * Other AST Helpers
         mkPrj, mapMAE, mapMAEWithEnv, mapMAEWithGEnv,

         -- * Helpers for constructing bits of AST syntax while incorporating small optimizations.
         addI, mulI, quotI, remI, maybeLet,         
         
         -- * Miscellaneous
         fragileZip,

         -- * Constants and functions for use in cost estimation:
         ifCost, derefCost, costPrim, costConst,
         defaultDupThreshold
         )
       where

import qualified Data.Map as M
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import Data.Array.Accelerate.BackendKit.Utils.EasyEmit as EE
import Text.PrettyPrint.HughesPJ as PP
import Foreign.Storable (sizeOf)
import qualified Prelude as P
import Prelude (error, ($), (.))
import Data.Int (Int)
import Data.Word (Word)
import Prelude ((++), show, return, Show)
import Control.Monad.State.Strict (State, get, put)
import Control.Applicative ((<$>),(<*>),pure,Applicative)

----------------------------------------------------------------------------------------------------
-- Conventions:
----------------------------------------------------------------------------------------------------

-- | During final C/OpenCL emission, create a name for a function that
-- executes a specific array operator.  That is, if you know the name
-- of an array variable, this will tell you what function to call to
-- populate that array.
builderName :: Var -> P.String
builderName vr = "build_" P.++ P.show vr


-- | Given the name of an array variable, what is the name of the
-- variable which will contain its shape.
shapeName :: Var -> Var
shapeName avr = S.var (P.show avr P.++ "_shape")

-- | Given the name of an array variable resulting from a
--   non-segmented FOLD, what is the name of a scalar variable
--   containing its stride.
strideName :: Var -> Var
strideName avr = S.var (P.show avr P.++ "_foldstride")


-- | Types for N-dimensional indices are just tuples of ints.
mkIndTy ::Int -> Type
mkIndTy n = mkTTuple (P.take n (P.repeat TInt))

-- | Is the type a tuple type, including unit?
isTupleTy :: Type -> P.Bool
isTupleTy t@(TTuple [_]) = error$"isTupleTy: corrupt type found, singleton tuple: "++show t
isTupleTy (TTuple _) = P.True
isTupleTy _          = P.False


-- | A monad to use just for gensyms:
type GensymM = State Int 

-- | Generate a unique name
genUnique :: GensymM Var
genUnique = genUniqueWith "gensym_"

-- | Generate a unique name with user-provided "meaningful" prefix.
genUniqueWith :: P.String -> GensymM Var
genUniqueWith prefix =
  do cnt <- get
     put (cnt+1)
     return$ S.var$ prefix ++ show cnt


----------------------------------------------------------------------------------------------------
-- Costing:
----------------------------------------------------------------------------------------------------

-- | The cost of a conditional IN ADDITOON to the cost of the two branches.
ifCost :: Int
ifCost = 1

-- | The cost of looking up an element in an array.
derefCost :: Int
derefCost = 1

-- | For now we use a constant cost across all primitive operations.
costPrim :: Prim -> Int
costPrim _ = 1

-- | For now we assume that all constants are free:
costConst :: Const -> Int
costConst _ = 1 

-- | If the cost of computing a single element of an array is less
-- than or equal to this threshold, that array may be /recomputed/
-- freely rather than precomputing it in the form of the original
-- array.  In practice this is used to determine when to inline
-- `Generate` and `BackPermute` array operations into their downstream
-- consumers.
defaultDupThreshold :: Int
defaultDupThreshold = 5


-- | Irrespective of the exact cost, certain expressions are
--   considered trivial (and always duplicatable).
-- isTrivialE 

----------------------------------------------------------------------------------------------------
-- Other Helpers
----------------------------------------------------------------------------------------------------

-- Safely make a projection, taking care not to project from a ONE
-- ELEMENT tuple (i.e. not a tuple):
mkPrj :: Int -> Int -> Int -> Exp -> Exp
mkPrj ind len total e | total P.<= 0 = 
  error$"mkPrj: something's wrong, total tuple size should not be "++show total++" expr: "++show (ETupProject ind len e)
mkPrj ind len total e | ind P.+ len P.> total = 
  error$"mkPrj: out of bounds tuple index, total "++show total++" expr: "++show (ETupProject ind len e)
mkPrj _ _ 1 e = e 
mkPrj ind len _total e = ETupProject ind len e 

-- Convenient integer operations
addI :: Exp -> Exp -> Exp
addI (EConst (I 0)) n = n
addI n (EConst (I 0)) = n
addI (EConst (I n)) (EConst (I m)) = EConst$ I$ n + m
addI n m              = EPrimApp TInt (NP Add) [n,m]

mulI :: Exp -> Exp -> Exp
mulI (EConst (I 0)) _ = EConst (I 0)
mulI _ (EConst (I 0)) = EConst (I 0)
mulI (EConst (I 1)) n = n
mulI n (EConst (I 1)) = n
mulI (EConst (I n)) (EConst (I m)) = EConst$ I$ n * m
mulI n m              = EPrimApp TInt (NP Mul) [n,m]

quotI :: Exp -> Exp -> Exp
quotI n (EConst (I 1)) = n
quotI (EConst (I n)) (EConst (I m)) = EConst$ I$ P.quot n m
quotI n m              = EPrimApp TInt (IP Quot) [n,m]

remI :: Exp -> Exp -> Exp
remI _ (EConst (I 1)) = EConst (I 0)
remI (EConst (I n)) (EConst (I m)) = EConst$ I$ P.rem n m
remI n m              = EPrimApp TInt (IP Rem) [n,m]

-- | Bind a let expression only if necessary.  Don't introduce
-- variable-variable copies.
maybeLet :: Exp -> Type -> (Var -> Exp) -> GensymM Exp
maybeLet ex ty dobod =
  case ex of
    EVr v -> return (dobod v)
    _ -> do tmp <- genUnique
            return (ELet (tmp,ty,ex) (dobod tmp))

-- | Do not allow the lists to be different lengths.
fragileZip :: (Show t1, Show t2) =>
              [t1] -> [t2] -> [(t1, t2)]
fragileZip a b = loop a b
  where
    loop [] []           = []
    loop (h1:t1) (h2:t2) = (h1,h2) : loop t1 t2
    loop _ _             = error$"JIT.hs/fragileZip: lists were not the same length: "++show a++" "++show b

--------------------------------------------------------------------------------
-- Traversals

-- | Map a monadic function over all Exps contained in an AExp.
mapMAE :: Applicative f => (Exp -> f Exp) -> AExp -> f AExp
mapMAE fn = mapMAEWithEnv M.empty (\ _ e -> fn e) 

-- | A variant of `mapMAE` that also tracks the variable-type binding
--   environment and passes it to the client function.
mapMAEWithEnv :: Applicative f => M.Map Var Type -> (M.Map Var Type -> Exp -> f Exp) -> AExp -> f AExp
mapMAEWithEnv env fn = mapMAEWithGEnv env (\ _ ty -> ty) fn

-- | Generalized version of `mapMAEWithEnv` that doesn't specify what is stored in the
-- environment.  The user provides a function to lift bindings into
-- the value they desire.
mapMAEWithGEnv :: Applicative f => M.Map Var v ->        
                  (Var -> Type -> v) ->             -- Lift a new binding into the environment.
                  (M.Map Var v -> Exp -> f Exp) ->  -- The function being mapped
                  AExp -> f AExp
mapMAEWithGEnv env lift fn0 ae =
  case ae of
    Use _                    -> pure ae
    Vr _                     -> pure ae
    Cond a b c               -> Cond     <$> fn a <*> pure b <*> pure c
    Generate e lam1          -> Generate <$> fn e <*> doLam1 lam1
    Unit ex                  -> Unit     <$> fn ex
    Map      lam1 vr         -> Map      <$> doLam1 lam1 <*> pure vr
    ZipWith  lam2 v1 v2      -> ZipWith  <$> doLam2 lam2 <*> pure v1 <*> pure v2
    Backpermute ex lam1 vr   -> Backpermute <$> fn ex <*> doLam1 lam1 <*> pure vr
    Replicate template ex vr -> Replicate template <$> fn ex <*> pure vr
    Reshape   shE v          -> Reshape  <$> fn shE <*> pure v
    Index slc vr ex          -> Index slc vr <$> fn ex
    Fold     lam2 e v        -> Fold     <$> doLam2 lam2 <*> fn   e <*> pure v
    Fold1    lam2 v          -> Fold1    <$> doLam2 lam2 <*> pure v
    FoldSeg  lam2 e v w      -> FoldSeg  <$> doLam2 lam2 <*> fn   e <*> pure v <*> pure w
    Fold1Seg lam2 v w        -> Fold1Seg <$> doLam2 lam2 <*> pure v <*> pure w
    Scanl    lam2 e v        -> Scanl    <$> doLam2 lam2 <*> fn   e <*> pure v
    Scanl'   lam2 e v        -> Scanl'   <$> doLam2 lam2 <*> fn   e <*> pure v
    Scanl1   lam2   v        -> Scanl1   <$> doLam2 lam2 <*> pure v
    Scanr    lam2 e v        -> Scanr    <$> doLam2 lam2 <*> fn   e <*> pure v
    Scanr'   lam2 e v        -> Scanr'   <$> doLam2 lam2 <*> fn   e <*> pure v
    Scanr1   lam2   v        -> Scanr1   <$> doLam2 lam2 <*> pure v
    Stencil  lam1 b v        -> Stencil  <$> doLam1 lam1 <*> pure b <*> pure v
    Stencil2 lam2 b v c w    -> Stencil2 <$> doLam2 lam2 <*> pure b <*> pure v 
                                                         <*> pure c <*> pure w
    Permute lam2 v lam1 w    -> Permute <$> doLam2 lam2 <*> pure v
                                        <*> doLam1 lam1 <*> pure w
 where
   fn = fn0 env
   doLam1 (Lam1 (v,t) bod)       = Lam1 (v,t)       <$> fn0 (M.insert v (lift v t) env) bod
   doLam2 (Lam2 (v,t) (w,u) bod) = Lam2 (v,t) (w,u) <$> fn0 (M.insert v (lift v t) $
                                                             M.insert w (lift w u) env) bod   



----------------------------------------------------------------------------------------------------
-- Emission:
----------------------------------------------------------------------------------------------------


-- | Emit a PrimApp provided that the operands have already been convinced to `Syntax`.
--   It returns EasyEmit `Syntax` representing a C expression.
--
--   The contract of this function is that the code generated by it
--   should be CAST to the expected type.
emitPrimApp :: Prim -> [Syntax] -> Syntax
emitPrimApp p args =
  case p of
    NP np -> case np of
              Add -> binop "+"
              Sub -> binop "-"
              Mul -> binop "*"
              Neg -> unary "-"
              Abs -> unary "abs"
              -- Warning, potential for code duplication here.  Should ensure that args are trivial:
              Sig ->  arg && (arg>0) && (-(arg<0))
    IP ip -> case ip of
              -- This uses the stdlib.h div function, not available in OpenCL:
              -- Quot -> (binfun "div") `dot` (constant "quot")
              -- Rem  -> (binfun "div") `dot` (constant "rem")
              Quot -> binop "/"
              Rem  -> binop "%"
              -- These two need to round towards negative infinity:
              IDiv -> error "integer division truncated towards negative infinity... not implemented yet!"
              Mod  -> error "integer modulus truncated towards negative infinity... not implemented yet!"
              BAnd -> binop "&"
              BOr  -> binop "|"
              BXor -> binop "^"
              BNot -> unary  "~"
              BShiftL -> binop "<<"
              BShiftR -> binop ">>"
              BRotateL -> (left << right) .| (left >> ((sizeof right) * 8 - 1))
              BRotateR -> (left >> right) .| (left << ((sizeof right) * 8 - 1))
    FP p -> case p of
              Recip -> EE.parens (1 / arg) 
              Sin  -> unary "sin"
              Cos  -> unary "cos"
              Tan  -> unary "tan"
              Asin -> unary "asin"
              Acos -> unary "acos"
              Atan -> unary "atan"
              Asinh -> unary "asinh"
              Acosh -> unary "acosh"
              Atanh -> unary "atanh"
              ExpFloating -> binop ""
              Sqrt  -> binop "sqrt"
              Log   -> binop "log" -- natural log
              FDiv    -> binop "/"
              FPow    -> binfun "expt"
              LogBase -> binop "log"
              Atan2   -> unary "atan2"
              Round   -> unary "round"
              Floor   -> unary "floor"
              Ceiling -> unary "ceil"
              -- The C CAST that should be wrapped around the esult of
              -- emitPrimApp should effectively truncate.
              Truncate -> arg
    SP p -> case p of
              Lt   -> binop "<"
              Gt   -> binop ">"
              LtEq -> binop "<="
              GtEq -> binop ">="
              Eq   -> binop "=="
              NEq  -> binop "!="
              Max  -> binfun "max"
              Min  -> binfun "min"
    BP p -> case p of
              And  -> binop "&&"
              Or   -> binop "||"
              Not  -> unary "!" 
    OP p -> case p of
              FromIntegral -> arg -- Again, depend on the cast.
              BoolToInt    -> arg
              Ord          -> arg
              S.Chr        -> arg
  where
   t = text
   [left,right] = args
   [arg]        = args -- laziness in action

   argD   = fromSyntax arg
   leftD  = fromSyntax left
   rightD = fromSyntax right
   
   binop op = left +++ toSyntax (text (" "++op++" ")) +++ right
   binfun op = toSyntax (text op <> PP.parens (leftD <> comma <> rightD))
   unary  op = toSyntax$ text op <> PP.parens argD


-- | Convert a type to the equivalent C type.
emitCType :: Type -> Syntax
-- NOTE! In the future this will have to grow more complex to track dimension:
emitCType (TArray dim elt) = emitCType elt +++ str "*"
emitCType ty = toSyntax$ text$ 
  case ty of
    TInt   -> "int"
    TInt8  -> "int8_t"
    TInt16 -> "int16_t"
    TInt32 -> "int32_t"
    TInt64 -> "int64_t"
    TWord   -> "unsigned int"
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
    TTuple [] -> "void"
    TTuple _  -> error "emitType: cannot handle tuples presently"

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

test0 = emitPrimApp (NP Sig) [constant "x"]
test1 = emitPrimApp (IP Quot) [constant "x", constant "y"]