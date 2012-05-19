
-- An example interpreter for the simplified AST.

module Data.Array.Accelerate.SimpleInterp
       (
       run 
       )
       where

import Data.Array.Accelerate.Smart                   (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import Data.Array.Accelerate.SimpleAST
import Data.Array.Accelerate.SimpleConverter (convertToSimpleAST)

import qualified Data.Map as M

import Data.Array.Unboxed ((!), UArray)
import qualified Data.Array.Unboxed as U
import qualified Data.Array         as A
import qualified Data.List as L

import Debug.Trace (trace)
tracePrint s x = trace (s++show x) x

--------------------------------------------------------------------------------
-- type Value = [AccArray]
type Env = M.Map Var Value
lookup = error"lookup"

data Value = TupVal [Value]
           | ArrVal AccArray
           | Scalar { unScalar :: Const }
  deriving Show           
--------------------------------------------------------------------------------

singleton (Scalar s) = ArrVal (error "finish me")

-- repackResult

run :: Sug.Arrays a => Acc a -> a
run acc = error (show (evalA M.empty (convertToSimpleAST acc)))


evalA :: Env -> AExp -> AccArray
evalA env ae = finalArr
  where 
   ArrVal finalArr = loop ae 
   loop :: AExp -> Value
   loop aexp =
     case aexp of 
       --     Vr Var -- Array variable bound by a Let.
       Vr  v             -> env M.! v
       Let vr ty lhs bod -> ArrVal$ evalA (M.insert vr (loop lhs) env) bod

       Unit e -> singleton (evalE M.empty e)
       ArrayTuple aes -> TupVal (map loop aes)

       Cond e1 ae2 ae3 -> case evalE env e1 of 
                            Scalar (B True)  -> loop ae2 
                            Scalar (B False) -> loop ae3

       Use _ty arr -> ArrVal arr
       Generate _ty eSz (Lam [(vr,_)] bodE) ->
       -- Indices can be arbitrary shapes:
         case evalE env eSz of 
           Scalar (I n) -> error "finish"
--           Scalar ()

         
       TupleRefFromRight i ae -> error "TupleRefFromRight"
       Apply afun ae -> error "Apply"
       Replicate slcty ex ae -> error "Replicate"
       Index     slcty ae ex -> error "Index"

       Map      fn ae         -> error "Map"
       ZipWith  fn ae1 ae2    -> error "ZipWith"
       
       -- Shave off leftmost dim in 'sh' list 
       -- (the rightmost dim in the user's (Z :. :.) expression):
       Fold     (Lam [(v1,_),(v2,_)] bodE) ex ae -> 
         trace ("FOLDING, shape "++show (innerdim:sh') ++ " lens "++ 
                show (alllens, L.group alllens) ++" arr "++show payloads++"\n") $ 
           case payloads of 
             [] -> error "Empty payloads!"
             _  -> ArrVal (AccArray sh' payloads')
         where initacc = evalE env ex
               AccArray (innerdim:sh') payloads = evalA env ae -- Must be >0 dimensional.
               payloads' = map (applyToPayload3 buildFolded) payloads               
               
               alllens = map payloadLength payloads
               len = case L.group alllens of
                      [len:_] -> len
                      x -> error$ "Corrupt Accelerate array.  Non-homogenous payload lengths: "++show x
               
               -- Cut the total size down by whatever the length of the inner dimension is:
               newlen = len `quot` innerdim

               buildFolded :: Int -> (Int -> Const) -> [Const]
               buildFolded _ lookup = tracePrint "\nbuildFOLDED : "$ 
                  [ unScalar (innerloop lookup (innerdim * i) innerdim initacc)
                  | i <- [0..newlen] ]

               -- The innermost dim is always contiguous in memory.
               innerloop :: (Int -> Const) -> Int -> Int -> Value -> Value
               innerloop _ _ 0 acc = acc
               innerloop lookup offset count acc = 
                 trace ("Inner looping "++show(offset,count,acc))$ 
                 innerloop lookup (offset+1) (count-1) $ 
                  evalE (M.insert v1 acc $ 
                         M.insert v2 (Scalar$ lookup offset) env) 
                        bodE 
       
       Fold1    fn ae         -> error "Foldl1"
       FoldSeg  fn ex ae1 ae2 -> error "FoldSeg"
       Fold1Seg fn    ae1 ae2 -> error "Fold1Seg" 
--   | Scanl    Fun Exp AExp        -- Scanl  Function InitialValue LinearArray
--   | Scanl'   Fun Exp AExp        -- Scanl' Function InitialValue LinearArray
--   | Scanl1   Fun     AExp        -- Scanl  Function              LinearArray
--   | Scanr    Fun Exp AExp        -- Scanr  Function InitialValue LinearArray
--   | Scanr'   Fun Exp AExp        -- Scanr' Function InitialValue LinearArray
--   | Scanr1   Fun     AExp        -- Scanr  Function              LinearArray
--   | Permute  Fun AExp Fun AExp   -- Permute CombineFun DefaultArr PermFun SourceArray
--   | Backpermute Exp Fun AExp     -- Backpermute ResultDimension   PermFun SourceArray
--   | Reshape     Exp     AExp     -- Reshape Shape Array
--   | Stencil  Fun Boundary AExp
--   | Stencil2 Fun Boundary AExp Boundary AExp -- Two source arrays/boundaries


-- -- | Apply a generic transformation to the Array Payload irrespective of element type.
-- applyToPayload :: (forall a . UArray Int a -> UArray Int a) -> ArrayPayload -> ArrayPayload
-- applyToPayload fn payl = 
--   case payl of 
--     ArrayPayloadInt    arr -> ArrayPayloadInt    (fn arr)
--     ArrayPayloadInt8   arr -> ArrayPayloadInt8   (fn arr)
--     ArrayPayloadInt16  arr -> ArrayPayloadInt16  (fn arr)
--     ArrayPayloadInt32  arr -> ArrayPayloadInt32  (fn arr) 
--     ArrayPayloadInt64  arr -> ArrayPayloadInt64  (fn arr)
--     ArrayPayloadWord   arr -> ArrayPayloadWord   (fn arr)
--     ArrayPayloadWord8  arr -> ArrayPayloadWord8  (fn arr) 
--     ArrayPayloadWord16 arr -> ArrayPayloadWord16 (fn arr)
--     ArrayPayloadWord32 arr -> ArrayPayloadWord32 (fn arr)
--     ArrayPayloadWord64 arr -> ArrayPayloadWord64 (fn arr)
--     ArrayPayloadFloat  arr -> ArrayPayloadFloat  (fn arr)
--     ArrayPayloadDouble arr -> ArrayPayloadDouble (fn arr)
--     ArrayPayloadChar   arr -> ArrayPayloadChar   (fn arr)
--     ArrayPayloadBool   arr -> ArrayPayloadBool   (fn arr) -- Word8's represent bools.


evalE :: Env -> Exp -> Value
evalE env expr = 
  case expr of 
    EVr  v             -> env M.! v
    ELet vr ty lhs bod -> evalE (M.insert vr (evalE env lhs) env) bod
    ETuple es          -> TupVal$ map (evalE env) es
    EConst c           -> Scalar c

    ECond e1 e2 e3     -> case evalE env e1 of 
                            Scalar (B True)  -> evalE env e2 
                            Scalar (B False) -> evalE env e3

    EIndexScalar ae ex -> indexArray (evalA env ae) (evalE env ex)
  
    EShape ae          -> let AccArray sh _ = evalA env ae 
                          in Scalar$ Tup $ map I sh
    
    EShapeSize exp     -> case evalE env exp of 
                            _ -> error "need more work on shapes"

    EPrimApp p es      -> evalPrim p (map (evalE env) es)

  -- | ETupProjectFromRight Int Exp  -- Project the nth field FROM THE RIGHT end of the tuple.  
  -- | EIndex [Exp] -- Index into a multi-dimensional array:
  -- | EIndexAny 
  -- | EIndexConsDynamic Exp Exp
  -- | EIndexHeadDynamic Exp 
  -- | EIndexTailDynamic Exp 
        

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------

indexArray = undefined


evalPrim :: Prim -> [Value] -> Value
evalPrim p [] = 
  case p of 
    NP Add -> Scalar (I 0)
      
evalPrim p es = 
  case p of 
    NP Add -> Scalar (foldl1 plus (map unScalar es))
        
plus :: Const -> Const -> Const
plus (I a) (I b) = I (a+b)
plus (F a) (F b) = F (a+b)
plus a b = error $ "plus: unmatched combination of values: "++show (a,b)

-- Todo: special constants: minBound, maxBound, pi

-- data Prim = NP NumPrim
--           | IP IntPrim
--           | FP FloatPrim
--           | SP ScalarPrim
--           | BP BoolPrim
--           | OP OtherPrim
--   deriving (Read,Show,Eq,Generic)
          
-- -- | Primitives that operate on /all/ numeric types.
-- --   Neg/Abs/Sig are unary:
-- data NumPrim = Add | Mul | Neg | Abs | Sig
--   deriving (Read,Show,Eq,Generic)

-- -- | Primitive integral-only operations.
-- -- All binops except BNot, shifts and rotates take an Int constant as second arg:
-- data IntPrim = Quot | Rem | IDiv | Mod | 
--                BAnd | BOr | BXor | BNot | BShiftL | BShiftR | BRotateL | BRotateR
--   deriving (Read,Show,Eq,Generic)

-- -- | Primitive floating point-only operations.
-- data FloatPrim = 
--       -- Unary:
--       Recip | Sin | Cos | Tan | Asin | Acos | Atan | Asinh | Acosh | Atanh | ExpFloating | Sqrt | Log |
--       -- Binary:                  
--       FDiv | FPow | LogBase | Atan2 | Truncate | Round | Floor | Ceiling
--   deriving (Read,Show,Eq,Generic)
           
-- -- | Relational and equality operators
-- data ScalarPrim = Lt | Gt | LtEq | GtEq | Eq | NEq | Max | Min
--   deriving (Read,Show,Eq,Generic)

-- data BoolPrim = And | Or | Not
--   deriving (Read,Show,Eq,Generic)

-- data OtherPrim = Ord | Chr | BoolToInt | FromIntegral
--   deriving (Read,Show,Eq,Generic)
