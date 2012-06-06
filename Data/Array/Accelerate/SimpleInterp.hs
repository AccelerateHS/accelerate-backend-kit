{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
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
import Data.Array.Accelerate.SimpleAST             as T
import Data.Array.Accelerate.SimpleArray           as SA
import Data.Array.Accelerate.SimpleConverter (convertToSimpleProg, packArray, repackAcc2)
import qualified Data.Map as M
import qualified Data.List as L

import Text.PrettyPrint.GenericPretty (Out(doc), Generic)

import Debug.Trace (trace)
tracePrint s x = trace (s++show x) x

--------------------------------------------------------------------------------
-- Exposing a standard Accelerate `run` interface.

-- | Run an Accelerate computation using a simple (and very
--   inefficient) interpreter.
run :: forall a . Sug.Arrays a => Acc a -> a
run acc = 
          trace ("[dbg] Repacking AccArray(s): "++show arrays) $ 
          repackAcc2 acc arrays
 where arrays = evalProg M.empty (convertToSimpleProg acc)

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
  deriving (Show, Generic)
           
instance Out Value

-- | Extract a `Const` from a `Value` if that is possible.
valToConst (ConstVal c ) = c
valToConst (TupVal ls)   = Tup $ map valToConst ls
valToConst (ArrVal a)    = error$ "cannot convert Array value to Const: "++show a

unConstVal (ConstVal c) = c 
unArrVal   (ArrVal v)   = v

--------------------------------------------------------------------------------
-- Evaluation:

-- | Evaluating a complete program creates a FLAT list of arrays as a
--   result.  Reimposing a nested structure to the resulting
--   tuple-of-arrays is not the job of this function.
evalProg :: Env -> S.Prog -> [AccArray]
evalProg origenv (S.Letrec binds results progtype) = 
    trace ("[dbg] evalProg, initial env "++ show (L.map (\(a,_,_)->a) binds)
           ++"  yielded environment: "++show (M.keys finalenv)) $
    L.map (unArrVal . (envLookup finalenv)) results
  where 
   finalenv = loop origenv binds
   -- A binding simply extends an environment of values. 
--   loop :: [(S.Var, S.Type, Either S.Exp S.AExp)] -> Env
   loop env [] = env
   loop env ((vr,ty,Left rhs):rst)  = loop (M.insert vr (evalE env rhs) env) rst
   loop env ((vr,ty,Right rhs):rst) = loop (doaexp env vr rhs) rst
   
   doaexp env vr rhs =   
     let bind rhs' = M.insert vr rhs' env in
     case rhs of
       S.Vr  v             -> bind$ envLookup env v
       S.Unit e -> case evalE env e of 
                    ConstVal c -> bind$ ArrVal$ SA.replicate [] c
                    oth  -> error$"evalProg: expecting ConstVal input to Unit, received: "++show oth
       S.Cond e1 v1 v2 -> case evalE env e1 of 
                             ConstVal (B True)  -> bind$ envLookup env v1
                             ConstVal (B False) -> bind$ envLookup env v2
       S.Use _ty arr -> bind$ ArrVal arr
       --------------------------------------------------------------------------------
       S.Generate (TArray _dim elty) eSz (S.Lam1 (vr,vty) bodE) ->
         trace ("[dbg] GENERATING: "++ show dims ++" "++ show elty) $ 
         
         -- It's tricky to support elementwise functions that produce
         -- tuples, which in turn need to be unpacked into a
         -- multi-payload array....
         bind $ ArrVal $ AccArray dims $ payloadsFromList elty $ 
         map (\ind -> valToConst $ evalE env (T.ELet (vr,vty,T.EConst ind) bodE)) 
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
       S.Replicate (TArray _dim elty) slcSig ex vr ->          
         trace ("[dbg] REPLICATING to "++show finalElems ++ " elems, newdims "++show newDims ++ " dims in "++show dimsIn) $
         trace ("[dbg]   replicatation index stream: "++show (map (map constToInteger . untuple) allIndices)) $ 
         if length dimsOut /= replicateDims || 
            length dimsIn  /= retainDims
         then error$ "replicate: replicating across "++show slcSig
                  ++ " dimensions whereas the first argument to replicate had dimension "++show dimsOut
         else if replicateDims == 0  -- This isn't a replication at all!
         then bind$ ArrVal $ inArray
         
         else bind$ ArrVal $ AccArray newDims $ 
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
           ArrVal (inArray@(AccArray dimsIn _)) = envLookup env vr
           
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
       S.Map (S.Lam1 (v,vty) bod) invr -> 
-- TODO!!! Handle maps that CHANGE the tupling...
--         trace ("MAPPING: over input arr "++ show inarr) $ 
         bind$ ArrVal$ mapArray evaluator inarr
         where  
           ArrVal inarr = envLookup env invr
           evaluator c = -- tracePrint ("In map, evaluating element "++ show c++" to ")$  
                         valToConst $ evalE env (T.ELet (v,vty, T.EConst c) bod)

       --------------------------------------------------------------------------------       
       S.ZipWith  (S.Lam2 (v1,vty1) (v2,vty2) bod) vr1 vr2  ->
         if dims1 /= dims2 
         then error$"zipWith: internal error, input arrays not the same dimension: "++ show dims1 ++" "++ show dims2
-- TODO: Handle the case where the resulting array is an array of tuples:
         else bind$ ArrVal$ AccArray dims1 final
         where 
           ArrVal (a1@(AccArray dims1 pays1)) = envLookup env vr1
           ArrVal (a2@(AccArray dims2 pays2)) = envLookup env vr2
           final = concatMap payloadsFromList1 $ 
                   L.transpose $ 
                   zipWith evaluator 
                           (L.transpose$ map payloadToList pays1)
                           (L.transpose$ map payloadToList pays2)
-- INCORRECT - we need to reassemble tuples here:
           evaluator cls1 cls2 = map valToConst $ untupleVal $ evalE env 
                                 (T.ELet (v1,vty1, T.EConst$ tuple cls1) $  
                                  T.ELet (v2,vty2, T.EConst$ tuple cls2) bod)

       --------------------------------------------------------------------------------       
       -- Shave off leftmost dim in 'sh' list 
       -- (the rightmost dim in the user's (Z :. :.) expression):
       S.Fold (S.Lam2 (v1,_) (v2,_) bodE) ex avr -> 
         -- trace ("FOLDING, shape "++show (innerdim:sh') ++ " lens "++ 
         --        show (alllens, L.group alllens) ++" arr "++show payloads++"\n") $ 
           case payloads of 
             [] -> error "Empty payloads!"
             _  -> bind$ ArrVal (AccArray sh' payloads')
         where initacc = evalE env ex
               ArrVal (AccArray (innerdim:sh') payloads) = envLookup env avr -- Must be >0 dimensional.
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
       S.Index     slcty  ae ex  -> error "UNFINISHED: Index"
       S.Fold1     fn ae         -> error "UNFINISHED: Foldl1"
       S.FoldSeg   fn ex ae1 ae2 -> error "UNFINISHED: FoldSeg"
       S.Fold1Seg  fn    ae1 ae2 -> error "UNFINISHED: Fold1Seg" 
       S.Scanl     fn ex ae      -> error "UNFINISHED: Scanl"
       S.Scanl'    fn ex ae      -> error "UNFINISHED: Scanl'"
       S.Scanl1    fn    ae      -> error "UNFINISHED: Scanl1"       
       S.Scanr     fn ex ae      -> error "UNFINISHED: Scanr"
       S.Scanr'    fn ex ae      -> error "UNFINISHED: Scanr'"
       S.Scanr1    fn    ae      -> error "UNFINISHED: Scanr1"       
       S.Permute  fn1 ae1 fn2 ae2 -> error "UNFINISHED: Permute"
       S.Backpermute  ex fn ae     -> error "UNFINISHED: Backpermute"
       S.Reshape      ex    ae     -> error "UNFINISHED: Reshape"
       S.Stencil      fn  bnd ae   -> error "UNFINISHED: Stencil"
       S.Stencil2  fn bnd1 ae1 bnd2 ae2 -> error "UNFINISHED: Stencil2"
       _ -> error$"Accelerate array expression breaks invariants: "++ show rhs

evalE :: Env -> T.Exp -> Value
evalE env expr = 
  case expr of 
    T.EVr  v             -> envLookup env v
    T.ELet (vr,_ty,lhs) bod -> evalE (M.insert vr (evalE env lhs) env) bod
    T.ETuple es          -> ConstVal$ Tup $ map (unConstVal . evalE env) es
    T.EConst c           -> ConstVal c

    T.ECond e1 e2 e3     -> case evalE env e1 of 
                            ConstVal (B True)  -> evalE env e2 
                            ConstVal (B False) -> evalE env e3

    T.EIndexScalar vr ex -> ConstVal$ indexArray (unArrVal$ envLookup env vr)
                             (map (fromIntegral . constToInteger) $ 
                              untuple$ valToConst$ evalE env ex)
  
    T.EShape vr          -> let ArrVal (AccArray sh _) = envLookup env vr
                            in ConstVal$ Tup $ map I sh
    
    T.EShapeSize ex      -> case evalE env ex of 
                            _ -> error "need more work on shapes"

    T.EPrimApp ty p es  -> evalPrim ty p (map (evalE env) es)

    T.ETupProjectFromRight ind ex -> 
      case (ind, evalE env ex) of 
        (_,ConstVal (Tup ls)) -> ConstVal$ reverse ls !! ind
        (ind,TupVal ls)       -> reverse ls !! ind
        (0,ConstVal scalar)   -> ConstVal$ scalar 
        (ind,const) -> error$ "ETupProjectFromRight: could not index position "
                       ++ show ind ++ " in tuple " ++ show const

    -- This is our chosen representation for index values:
    T.EIndex indls       -> let ls = map (valToConst . evalE env) indls in
                          ConstVal$ tuple ls
    
--    EIndexAny          -> error "UNFINISHED: evalE of EIndexAny - not implemented"
    T.EIndexConsDynamic e1 e2 -> case (evalE env e1, evalE env e2) of
                                 (ConstVal c1, ConstVal c2) -> ConstVal (Tup (c1 : untuple c2))
                                   
    T.EIndexHeadDynamic ex    -> case evalE env ex of 
                                 ConstVal (Tup ls) -> ConstVal (head ls)
                                 ConstVal c        -> ConstVal c 
                                 oth -> error$ "EIndexHeadDynamic, unhandled: "++ show oth
    T.EIndexTailDynamic ex    -> case evalE env ex of 
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

tupleVal :: [Value] -> Value
tupleVal [x] = x
tupleVal ls  = TupVal ls

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
    
    SP Gt -> ConstVal (gt (valToConst x) (valToConst y))

    oth -> error$"evalPrim needs to handle "++show oth

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


gt :: Const -> Const -> Const
#define GT(X) gt (X a) (X b) = B (a < b);
GT(I) GT(I8) GT(I16) GT(I32) GT(I64) 
GT(W) GT(W8) GT(W16) GT(W32) GT(W64) 
GT(F) GT(D)  GT(CF)  GT(CD)
GT(CS)  GT(CI)  GT(CL)  GT(CLL) 
GT(CUS) GT(CUI) GT(CUL) GT(CULL) 
GT(CC)  GT(CUC) GT(CSC)
gt a b = error $ "gt: unsupported combination of values: "++show(a,b)



-- data BoolPrim = And | Or | Not


-- data OtherPrim = Ord | Chr | BoolToInt | FromIntegral

