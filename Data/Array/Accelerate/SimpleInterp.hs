
-- An example interpreter for the simplified AST.

module Data.Array.Accelerate.SimpleInterp
       (
       run 
       )
       where

import Data.Array.Accelerate.SimpleAST
import Data.Array.Accelerate.SimpleConverter (convertToSimpleAST)

import qualified Data.Map as M

--------------------------------------------------------------------------------
-- type Value = [AccArray]
type Env = M.Map Var Value
lookup = undefined

data Value = TupVal [Value]
           | ArrVal AccArray
           | Scalar { unScalar :: Const }
--------------------------------------------------------------------------------

singleton (Scalar s) = ArrVal (error "finish me")

-- repackResult

run = undefined


evalA :: Env -> AExp -> AccArray
evalA env ae = finalArr
  where 
   ArrVal finalArr = loop ae 
   loop :: AExp -> Value
   loop ae =
     case ae of 
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
           _ -> error "finish"

         
--   | TupleRefFromRight Int AExp     
--   | Apply AFun AExp              -- Function $ Argument


--   | Replicate SliceType Exp AExp -- Replicate array across one or more dimensions.
--   | Index     SliceType AExp Exp -- Index a sub-array (slice).
--                                  -- Index sliceIndex Array SliceDims
--   | Map      Fun AExp            -- Map Function Array
--   | ZipWith  Fun AExp AExp       -- ZipWith Function Array1 Array2
--   | Fold     Fun Exp AExp        -- Fold Function Default Array
--   | Fold1    Fun AExp            -- Fold1 Function Array
--   | FoldSeg  Fun Exp AExp AExp   -- FoldSeg Function Default Array 'Segment Descriptor'
--   | Fold1Seg Fun     AExp AExp   -- FoldSeg Function         Array 'Segment Descriptor'
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
  
    EShape ae          -> case evalA env ae of
                            ArrayUnit -> error "TODO: AccArray needs to carry shape!"
    
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
