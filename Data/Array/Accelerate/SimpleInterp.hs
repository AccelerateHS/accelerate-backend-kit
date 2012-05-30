{-# LANGUAGE CPP, ScopedTypeVariables #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- An example interpreter for the simplified AST.

module Data.Array.Accelerate.SimpleInterp
       (
       run 
       )
       where

import Data.Array.Accelerate.Smart                   (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import Data.Array.Accelerate.SimpleAST             as S
import Data.Array.Accelerate.SimpleArray           as SA
import Data.Array.Accelerate.SimpleConverter (convertToSimpleAST, packArray, repackAcc)

import qualified Data.Map as M

import Data.Array.Unboxed ((!), UArray)
import qualified Data.Array.Unboxed as U
import qualified Data.Array         as A
import qualified Data.List as L

import Debug.Trace (trace)
tracePrint s x = trace (s++show x) x

--------------------------------------------------------------------------------
-- Exposing a standard Accelerate `run` interface.

-- | Run an Accelerate computation using a simple (and very
--   inefficient) interpreter.
run :: forall a . Sug.Arrays a => Acc a -> a
run acc = 
          trace ("[dbg] Repacking AccArray: "++show array) $ 
          repackAcc acc array
 where array = evalA M.empty (convertToSimpleAST acc)

--------------------------------------------------------------------------------
-- Values and Environments:

type Env = M.Map Var Value
envLookup env vr = 
  case M.lookup vr env of 
    Just x -> x 
    Nothing -> error$ "envLookup: no binding for variable "++show vr

-- | The value representation for the interpreter.
-- 
-- /Convention:/  Multidimensional index values are represented as a
-- const tuple of scalars.
data Value = TupVal [Value]
           | ArrVal AccArray
           | ConstVal Const 
  deriving Show           


-- | Extract a `Const` from a `Value` if that is possible.
valToConst (ConstVal c ) = c
valToConst (TupVal ls)   = Tup $ map valToConst ls
valToConst (ArrVal a)    = error$ "cannot convert Array value to Const: "++show a

--------------------------------------------------------------------------------
-- Evaluation:

evalA :: Env -> AExp -> AccArray
evalA env ae = 
    trace ("[dbg] evalA with environment: "++show env++"\n    "++show ae)
    finalArr
  where 
   ArrVal finalArr = loop ae 

   loop :: AExp -> Value
   loop aexp =
     case aexp of 
       --     Vr Var -- Array variable bound by a Let.
       Vr  v             -> envLookup env v
       Let vr ty lhs bod -> ArrVal$ evalA (M.insert vr (loop lhs) env) bod

       Unit e -> case evalE env e of 
                   ConstVal c -> ArrVal$ SA.replicate [] c
       ArrayTuple aes -> TupVal (map loop aes)

       Cond e1 ae2 ae3 -> case evalE env e1 of 
                            ConstVal (B True)  -> loop ae2 
                            ConstVal (B False) -> loop ae3

       Use _ty arr -> ArrVal arr
       Generate (TArray _dim elty) eSz (Lam [(vr,vty)] bodE) ->
         trace ("[dbg] GENERATING: "++ show dims ++" "++ show elty) $ 
         
         -- It's tricky to support elementwise functions that produce
         -- tuples, which in turn need to be unpacked into a
         -- multi-payload array....
         ArrVal $ AccArray dims $ payloadsFromList elty $ 
         map (\ind -> valToConst $ evalE env (ELet vr vty (EConst ind) bodE)) 
             (indexSpace dims)
                  
         where 
           dims = 
             -- Indices can be arbitrary shapes:
             case evalE env eSz of 
               ConstVal (I n)    -> [n]
               ConstVal (Tup ls) -> map (\ (I i) -> i) ls
         
       --------------------------------------------------------------------------------
                              
       -- One way to think of the slice descriptor fed to replicate is
       -- it contains exactly as many "All"s as there are dimensions
       -- in the input.  These All's are replaced, in order, by input
       -- dimensions.  
       -- 
       -- "Fixed" dimensions on the other hand are the replication
       -- dimensions.  Varying indices in those dimensions will not
       -- change the value contained in the indexed slot in the array.
       Replicate (TArray _dim elty) slcSig ex ae ->          
         trace ("[dbg] REPLICATING to "++show finalElems ++ " elems, newdims "++show newDims ++ " dims in "++show dimsIn) $
         trace ("[dbg]   replicatation index stream: "++show (map (map constToInteger . untuple) allIndices)) $ 
         if length dimsOut /= replicateDims || 
            length dimsIn  /= retainDims
         then error$ "replicate: replicating across "++show slcSig
                  ++ " dimensions whereas the first argument to replicate had dimension "++show dimsOut
         else if replicateDims == 0  -- This isn't a replication at all!
         then ArrVal $ inArray
         
         else ArrVal $ AccArray newDims $ 
              payloadsFromList elty $ 
              map (\ ind -> let intind = map (fromIntegral . constToInteger) (untuple ind) in 
                            indexArray inArray (unliftInd intind))
                  allIndices
        where
           allIndices = indexSpace newDims
           newDims    = injectDims dimsIn slcSig dimsOut
           replicateDims = length $ filter (== Fixed) slcSig
           retainDims    = length $ filter (== All)   slcSig
           -- These are ONLY the new replicated dimensions (excluding All fields):
           dimsOut = case evalE env ex of 
                      ConstVal s | isIntConst s -> [fromIntegral$ constToInteger s]
                      ConstVal (Tup ls) -> 
                        map (fromIntegral . constToInteger) $ 
                        filter isNumConst ls
                      oth -> error $ "replicate: bad first argument to replicate: "++show oth
           inArray@(AccArray dimsIn _) = evalA env ae
           
           -- The number of final elements is the starting elements times the degree of replication:
           finalElems = foldl (*) 1 dimsIn * 
                        foldl (*) 1 dimsOut
           
           -- Insert the new dimensions where "Any"s occur.
           injectDims :: [Int] -> SliceType -> [Int] -> [Int]
           injectDims [] [] [] = []
           injectDims (dim:l1) (All : l2)    l3       = dim : injectDims l1 l2 l3
           injectDims l1       (Fixed : l2)  (dim:l3) = dim : injectDims l1 l2 l3
           injectDims l1 l2 l3 = error$ "injectDims: bad input: "++ show (l1,l2,l3)

           -- Take an index (represented as [Int]) into the larger,
           -- replicated, index space and project it back into the
           -- originating index space.
           unliftInd :: [Int] -> [Int]
           unliftInd = unliftLoop slcSig 
           unliftLoop [] [] = []
           unliftLoop (Fixed:ssig) (_:inds) =     unliftLoop ssig inds 
           unliftLoop (All:ssig)   (i:inds) = i : unliftLoop ssig inds


           
       --------------------------------------------------------------------------------
       Map (Lam [(v,vty)] bod) ae -> 
-- TODO!!! Handle maps that change the tupling...
         
--         trace ("MAPPING: over input arr "++ show inarr) $ 
         ArrVal$ mapArray evaluator inarr
         where  
           inarr = evalA env ae
           evaluator c = -- tracePrint ("In map, evaluating element "++ show c++" to ")$  
                         valToConst $ evalE env (ELet v vty (EConst c) bod)
         
       ZipWith  (Lam [(v1,vty1), (v2,vty2)] bod) ae1 ae2  ->
         if dims1 /= dims2 
         then error$"zipWith: internal error, input arrays not the same dimension: "++ show dims1 ++" "++ show dims2
-- TODO: Handle the case where the resulting array is an array of tuples:
         else ArrVal$ AccArray dims1 final
         where 
           a1@(AccArray dims1 pays1) = evalA env ae1
           a2@(AccArray dims2 pays2) = evalA env ae2
           final = concatMap payloadsFromList1 $ 
                   L.transpose $ 
                   zipWith evaluator 
                           (L.transpose$ map payloadToList pays1)
                           (L.transpose$ map payloadToList pays2)
-- INCORRECT - we need to reassemble tuples here:
           evaluator cls1 cls2 = map valToConst $ untupleVal $ evalE env 
                                 (ELet v1 vty1 (EConst$ tuple cls1) $  
                                  ELet v2 vty2 (EConst$ tuple cls2) bod)

       --------------------------------------------------------------------------------       
       -- Shave off leftmost dim in 'sh' list 
       -- (the rightmost dim in the user's (Z :. :.) expression):
       Fold     (Lam [(v1,_),(v2,_)] bodE) ex ae -> 
         -- trace ("FOLDING, shape "++show (innerdim:sh') ++ " lens "++ 
         --        show (alllens, L.group alllens) ++" arr "++show payloads++"\n") $ 
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
               buildFolded _ lookup = 
--                  tracePrint "\nbuildFOLDED : "$ 
                  [ valToConst (innerloop lookup (innerdim * i) innerdim initacc)
                  | i <- [0..newlen] ]

               -- The innermost dim is always contiguous in memory.
               innerloop :: (Int -> Const) -> Int -> Int -> Value -> Value
               innerloop _ _ 0 acc = acc
               innerloop lookup offset count acc = 
--                 trace ("Inner looping "++show(offset,count,acc))$ 
                 innerloop lookup (offset+1) (count-1) $ 
                  evalE (M.insert v1 acc $ 
                         M.insert v2 (ConstVal$ lookup offset) env) 
                        bodE 
       
       Index     slcty  ae ex -> error "UNFINISHED: Index"
       TupleRefFromRight i ae -> error "UNFINISHED: TupleRefFromRight"
       Apply afun ae          -> error "UNFINISHED: Apply"


       Fold1    fn ae         -> error "UNFINISHED: Foldl1"
       FoldSeg  fn ex ae1 ae2 -> error "UNFINISHED: FoldSeg"
       Fold1Seg fn    ae1 ae2 -> error "UNFINISHED: Fold1Seg" 
       Scanl    fn ex ae      -> error "UNFINISHED: Scanl"
       Scanl'   fn ex ae      -> error "UNFINISHED: Scanl'"
       Scanl1   fn    ae      -> error "UNFINISHED: Scanl1"       
       Scanr    fn ex ae      -> error "UNFINISHED: Scanr"
       Scanr'   fn ex ae      -> error "UNFINISHED: Scanr'"
       Scanr1   fn    ae      -> error "UNFINISHED: Scanr1"       
       Permute fn1 ae1 fn2 ae2 -> error "UNFINISHED: Permute"
       Backpermute ex fn ae     -> error "UNFINISHED: Backpermute"
       Reshape     ex    ae     -> error "UNFINISHED: Reshape"
       Stencil     fn  bnd ae   -> error "UNFINISHED: Stencil"
       Stencil2 fn bnd1 ae1 bnd2 ae2 -> error "UNFINISHED: Stencil2"

       _ -> error$"Accelerate array expression breaks invariants: "++ show aexp

evalE :: Env -> Exp -> Value
evalE env expr = 
  case expr of 
    EVr  v             -> envLookup env v
    ELet vr _ty lhs bod -> evalE (M.insert vr (evalE env lhs) env) bod
    ETuple es          -> TupVal$ map (evalE env) es
    EConst c           -> ConstVal c

    ECond e1 e2 e3     -> case evalE env e1 of 
                            ConstVal (B True)  -> evalE env e2 
                            ConstVal (B False) -> evalE env e3

    EIndexScalar ae ex -> ConstVal$ indexArray (evalA env ae) 
                           (map (fromIntegral . constToInteger) $ 
                            untuple$ valToConst$ evalE env ex)
  
    EShape ae          -> let AccArray sh _ = evalA env ae 
                          in ConstVal$ Tup $ map I sh
    
    EShapeSize ex      -> case evalE env ex of 
                            _ -> error "need more work on shapes"

    EPrimApp ty p es  -> evalPrim ty p (map (evalE env) es)

    ETupProjectFromRight ind ex -> 
      case (ind, evalE env ex) of 
        (_,ConstVal (Tup ls)) -> ConstVal$ reverse ls !! ind
        (ind,TupVal ls)       -> reverse ls !! ind
        (0,ConstVal scalar)   -> ConstVal$ scalar 
        (ind,const) -> error$ "ETupProjectFromRight: could not index position "
                       ++ show ind ++ " in tuple " ++ show const

    -- This is our chosen representation for index values:
    EIndex indls       -> let ls = map (valToConst . evalE env) indls in
                          ConstVal$ tuple ls
    
    EIndexAny          -> error "UNFINISHED: evalE of EIndexAny"
    EIndexConsDynamic e1 e2 -> case (evalE env e1, evalE env e2) of
                                 (ConstVal c1, ConstVal c2) -> ConstVal (Tup (c1 : untuple c2))
                                   
    EIndexHeadDynamic ex    -> case evalE env ex of 
                                 ConstVal (Tup ls) -> ConstVal (head ls)
                                 ConstVal c        -> ConstVal c 
                                 oth -> error$ "EIndexHeadDynamic, unhandled: "++ show oth
    EIndexTailDynamic ex    -> case evalE env ex of 
                                 ConstVal (Tup ls) -> ConstVal (Tup (tail ls))
                                 oth -> error$ "EIndexTailDynamic, unhandled: "++ show oth

--------------------------------------------------------------------------------

-- | Create a list of Const/int indices corresponding to the index space
--   of an Accelerate array, layed out in the appropriate order for
--   Accelerate.  
--                                  
-- Note that indices in this interpreter are in REVERSE ORDER from
-- Accelerate source code.  The fastest changing dimension is the LEFTMOST.
indexSpace :: [Int] -> [Const]
indexSpace inds = map (tuple . reverse) $ 
                  loop (reverse inds)
  where 
    loop :: [Int] -> [[Const]]
    loop []  = []
    loop [n] = map (\i -> [I i]) [0..n-1]
    loop (hd:tl) = 
      let rest = loop tl in
      concatMap (\ i -> map (I i:) rest)
                [0..hd-1]
  -- map I [0..n-1]
           

-- Unary tuples do not exist in the language:
tuple :: [Const] -> Const
tuple [x] = x
tuple ls  = Tup ls

-- This currently handles nested Tups, but we generally insure those won't occur:
untuple :: Const -> [Const]
untuple (Tup ls) = concatMap untuple ls
untuple oth = [oth]

-- This goes inside both types of tuples (Val and Const).
untupleVal :: Value -> [Value]
untupleVal (TupVal ls)  = concatMap untupleVal ls
untupleVal (ConstVal c) = map ConstVal $ untuple c
untupleVal (ArrVal a)   = [ArrVal a]


--------------------------------------------------------------------------------

evalPrim :: Type -> Prim -> [Value] -> Value
-- evalPrim ty p [] = 
--   case p of 
--     NP Add -> ConstVal (I 0)
      
evalPrim ty p [x,y] = 
  case p of 
--    NP Add -> ConstVal (foldl1 add (map valToConst es))
--    NP Mul -> ConstVal (foldl1 mul (map valToConst es))
--    NP Neg -> ConstVal (neg  $ valToConst $ head es)
--    NP Abs -> ConstVal (absv $ valToConst $ head es)
--    NP Sig -> ConstVal (sig  $ valToConst $ head es)
    
    NP Add -> ConstVal (add (valToConst x) (valToConst y))
    NP Mul -> ConstVal (mul (valToConst x) (valToConst y))
    
evalPrim ty p [x] = 
  case p of 
    NP Neg -> ConstVal (neg  $ valToConst x)
    NP Abs -> ConstVal (absv $ valToConst x)
    NP Sig -> ConstVal (sig  $ valToConst x)

--           | IP IntPrim
--           | FP FloatPrim
--           | SP ScalarPrim
--           | BP BoolPrim
--           | OP OtherPrim
    OP FromIntegral -> ConstVal $       
      case ty of 
        TFloat  -> F$ fromConst (valToConst x)
        TDouble -> D$ fromConst (valToConst x)
--      error "evalPrim: Need more type information to implement this..."

    _ -> error$"UNFINISHED: evalPrim needs to be extended to handle all primitives: "++show p


add :: Const -> Const -> Const
#define ADD(X) add (X a) (X b) = X (a+b);
ADD(I) ADD(I8) ADD(I16) ADD(I32) ADD(I64) 
ADD(W) ADD(W8) ADD(W16) ADD(W32) ADD(W64) 
ADD(F) ADD(D)  ADD(CF)  ADD(CD)
ADD(CS)  ADD(CI)  ADD(CL)  ADD(CLL) 
ADD(CUS) ADD(CUI) ADD(CUL) ADD(CULL) 
ADD(CC)  ADD(CUC) ADD(CSC)
add a b = error $ "add: unsupported combination of values: "++show (a,b)

mul :: Const -> Const -> Const
#define MUL(X) mul (X a) (X b) = X (a*b); 
MUL(I) MUL(I8) MUL(I16) MUL(I32) MUL(I64) 
MUL(W) MUL(W8) MUL(W16) MUL(W32) MUL(W64) 
MUL(F) MUL(D)  MUL(CF)  MUL(CD)
MUL(CS)  MUL(CI)  MUL(CL)  MUL(CLL) 
MUL(CUS) MUL(CUI) MUL(CUL) MUL(CULL) 
MUL(CC)  MUL(CUC) MUL(CSC)
mul a b = error $ "mul: unsupported combination of values: "++show(a,b)

neg :: Const -> Const
#define NEG(X) neg (X a) = X (- a);
NEG(I) NEG(I8) NEG(I16) NEG(I32) NEG(I64) 
NEG(W) NEG(W8) NEG(W16) NEG(W32) NEG(W64) 
NEG(F) NEG(D)  NEG(CF)  NEG(CD)
NEG(CS)  NEG(CI)  NEG(CL)  NEG(CLL) 
NEG(CUS) NEG(CUI) NEG(CUL) NEG(CULL) 
NEG(CC)  NEG(CUC) NEG(CSC)
neg a = error $ "negate: unsupported value: "++show a

absv :: Const -> Const
#define ABS(X) absv (X a) = X (Prelude.abs a);
ABS(I) ABS(I8) ABS(I16) ABS(I32) ABS(I64) 
ABS(W) ABS(W8) ABS(W16) ABS(W32) ABS(W64) 
ABS(F) ABS(D)  ABS(CF)  ABS(CD)
ABS(CS)  ABS(CI)  ABS(CL)  ABS(CLL) 
ABS(CUS) ABS(CUI) ABS(CUL) ABS(CULL) 
ABS(CC)  ABS(CUC) ABS(CSC)
absv a = error $ "abs: unsupported value: "++show a

sig :: Const -> Const
#define SIG(X) sig (X a) = X (signum a);
SIG(I) SIG(I8) SIG(I16) SIG(I32) SIG(I64) 
SIG(W) SIG(W8) SIG(W16) SIG(W32) SIG(W64) 
SIG(F) SIG(D)  SIG(CF)  SIG(CD)
SIG(CS)  SIG(CI)  SIG(CL)  SIG(CLL) 
SIG(CUS) SIG(CUI) SIG(CUL) SIG(CULL) 
SIG(CC)  SIG(CUC) SIG(CSC)
sig a = error $ "sig: unsupported value: "++show a



        
-- data IntPrim = Quot | Rem | IDiv | Mod | 
--                BAnd | BOr | BXor | BNot | BShiftL | BShiftR | BRotateL | BRotateR


-- data FloatPrim = 
--       -- Unary:
--       Recip | Sin | Cos | Tan | Asin | Acos | Atan | Asinh | Acosh | Atanh | ExpFloating | Sqrt | Log |
--       -- Binary:                  
--       FDiv | FPow | LogBase | Atan2 | Truncate | Round | Floor | Ceiling

           

-- data ScalarPrim = Lt | Gt | LtEq | GtEq | Eq | NEq | Max | Min




-- data BoolPrim = And | Or | Not


-- data OtherPrim = Ord | Chr | BoolToInt | FromIntegral

