{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
-- {-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | An UNFINISHED example interpreter for the simplified AST defined in "Data.Array.Accelerate.SimpleAST".
-- 
module Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter
       (
         -- * Main module entrypoints  
         run, evalSimpleAcc,
         interpBackend,
         -- SimpleInterpBackend,
         
         -- * Smaller pieces that may be useful
         evalPrim, 
         evalE,
         Value(..), valToConst, unConstVal, unArrVal, 
       )
       where

-- import qualified Data.Array.Accelerate as A
import           Data.Array.Accelerate.BackendKit.Utils.Helpers    (maybtrace, tracePrint)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1, repackAcc)
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as T
import           Data.Array.Accelerate.BackendKit.SimpleArray   as SA
import qualified Data.Array.Accelerate.Array.Sugar              as Sug
import qualified Data.Array.Accelerate.AST                      as AST
import           Data.Array.Accelerate.Smart           (Acc)
import qualified Data.List as L
import qualified Data.Map  as M
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)

import Data.Array.Accelerate.BackendClass (Backend(..), SimpleBackend(..), MinimalBackend(..))

interpBackend :: MinimalBackend
interpBackend = MinimalBackend run'

-- | A unit type just to carry a `SimpleBackend` and `Backend` instance.
data SimpleInterpBackend = SimpleInterpBackend 
  deriving (Show,Eq,Ord,Read)

{-
instance SimpleBackend SimpleInterpBackend where
  type SimpleRemote SimpleInterpBackend = ()
  type SimpleBlob SimpleInterpBackend   = ()
  simpleCompile SimpleInterpBackend _ _ = return ()
--  simpleRunRaw SimpleInterpBackend nm acc mb = simpleRunRaw b nm acc mb
  -- simpleCopyToHost SimpleInterpBackend r     = simpleCopyToHost b r 
  -- simpleCopyToDevice SimpleInterpBackend a   = simpleCopyToDevice b a
  -- simpleCopyToPeer SimpleInterpBackend r     = simpleCopyToPeer b r
  -- simpleWaitRemote SimpleInterpBackend r     = simpleWaitRemote b r
  -- simpleUseRemote SimpleInterpBackend r      = simpleUseRemote b r
  -- simpleSeparateMemorySpace SimpleInterpBackend = simpleSeparateMemorySpace b
  -- simpleCompileFun1 SimpleInterpBackend = simpleCompileFun1 b
  -- simpleRunRawFun1  SimpleInterpBackend = simpleRunRawFun1 b

instance Backend SimpleInterpBackend where
  data Remote SimpleInterpBackend  r = SIB_Remote !r
  data Blob   SimpleInterpBackend _r = SIB_Blob

  compile _ _ _     = return SIB_Blob
  compileFun1 _ _ _ = return SIB_Blob

  runRaw SimpleInterpBackend acc _mblob = 
    return $! SIB_Remote (run' acc)

  copyToHost _ (SIB_Remote rm) = return $! rm
  copyToDevice _ a = return $! SIB_Remote a
  copyToPeer _ rm = return $! rm

  waitRemote _ _ = return ()
  useRemote _ (SIB_Remote r) = return $! phase0 (A.use r)
  separateMemorySpace _ = False -- This is pretty bogus, we have no idea.

-}

--------------------------------------------------------------------------------
-- Exposing a standard Accelerate `run` interface.

-- | Run an Accelerate computation using a simple (and very
--   inefficient) interpreter.
run :: forall a . Sug.Arrays a => Acc a -> a
run = run' . phase0 

-- | Version that works on post-converted Accelerate programs.
run' :: forall a . Sug.Arrays a => AST.Acc a -> a
run' acc = 
          maybtrace ("[dbg] Repacking AccArray(s): "++show arrays) $ 
          repackAcc (undefined :: Acc a) arrays
 where arrays = evalSimpleAcc (phase1 acc)

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

unConstVal :: Value -> Const 
unConstVal (ConstVal c) = c

unArrVal :: Value -> AccArray
unArrVal   (ArrVal v)   = v

--------------------------------------------------------------------------------
-- Evaluation:

-- | Evaluating a complete program creates a FLAT list of arrays as a
--   result.  Reimposing a nested structure to the resulting
--   tuple-of-arrays is not the job of this function.
evalSimpleAcc :: S.Prog a -> [AccArray]
evalSimpleAcc (S.Prog {progBinds, progResults}) = 
--    concatArrays $ 
    maybtrace ("[dbg] evalSimpleAcc, initial env "++ show (L.map (\(ProgBind v _ _ _)->v) progBinds)
           ++"  yielded environment: "++show (M.keys finalenv)) $
    L.map (unArrVal . (envLookup finalenv)) (resultNames progResults)
  where 
   finalenv = loop M.empty progBinds
   -- A binding simply extends an environment of values. 
--   loop :: [(S.Var, S.Type, Either S.Exp S.AExp)] -> Env
   loop env [] = env
   loop env (ProgBind vr ty _ (Left rhs)  :rst) = loop (M.insert vr (evalE env rhs) env) rst
   loop env (ProgBind vr ty _ (Right rhs) :rst) = loop (doaexp env vr ty rhs) rst
   
   doaexp env vr (TArray _dim elty) rhs =   
     let bind rhs' = M.insert vr rhs' env in
     case rhs of
       S.Vr  v             -> bind$ envLookup env v
       S.Unit e -> case evalE env e of 
                    ConstVal c -> bind$ ArrVal$ SA.replicate [] c
                    oth  -> error$"evalSimpleAcc: expecting ConstVal input to Unit, received: "++show oth
       S.Cond e1 v1 v2 -> case evalE env e1 of 
                             ConstVal (B True)  -> bind$ envLookup env v1
                             ConstVal (B False) -> bind$ envLookup env v2
       S.Use arr -> bind$ ArrVal arr
       --------------------------------------------------------------------------------
       S.Generate eSz (S.Lam1 (vr,vty) bodE) ->
         maybtrace ("[dbg] GENERATING: "++ show dims ++" "++ show elty) $ 
         
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
       S.Replicate slcSig ex vr ->          
         maybtrace ("[dbg] REPLICATING to "++show finalElems ++ " elems, newdims "++show newDims ++ " dims in "++show dimsIn) $
         maybtrace ("[dbg]   replicatation index stream: "++show (map (map constToInteger . untuple) allIndices)) $ 
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
           
           -- Insert the new dimensions where "All"s occur.
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
    T.ELet (vr,_ty,rhs) bod -> maybtrace ("[dbg]  ELet: bound "++show vr++" to "++show rhs') $
                               evalE (M.insert vr rhs' env) bod
                               where rhs' = (evalE env rhs)
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

    T.EPrimApp ty p es  -> ConstVal$ evalPrim ty p (map (valToConst . evalE env) es)

    T.ETupProject ind len ex -> 
      tracePrint ("[dbg]  ETupProject: "++show ind++" "++show len++": ") $
      case (ind, len, evalE env ex) of 
        (_,_,ConstVal (Tup ls)) -> ConstVal$ tuple$  slice ls 
        -- TODO -- check if this makes sense ... how can we run into this kind of tuple?:
        (ind,_,TupVal ls)       -> tupleVal$ slice ls
        (0,1,ConstVal scalar)   -> ConstVal$ scalar 
        (_,_,const) -> error$ "ETupProjectFromRight: could not index "++show len++" elements at position "
                       ++ show ind ++ " in tuple " ++ show const
      where slice ls = reverse $ take len $ drop ind $ reverse ls

    -- This is our chosen representation for index values:
    T.EIndex indls       -> let ls = map (valToConst . evalE env) indls in
                          ConstVal$ tuple ls

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

evalPrim :: Type -> Prim -> [Const] -> Const
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
    
    NP Add -> add x y
    NP Mul -> mul x y
    SP Gt  -> gt x y
    oth -> error$"evalPrim needs to handle "++show oth

evalPrim ty p [c] = 
  case p of 
    NP Neg -> neg  c
    NP Abs -> absv c
    NP Sig -> sig  c
--           | IP IntPrim
--           | FP FloatPrim
--           | SP ScalarPrim
--           | BP BoolPrim
--           | OP OtherPrim
    OP FromIntegral ->
      -- Here we need to convert to the right kind of constant:
      let err = error$"bad type of input to FromIntegral: "++show ty in
      case ty of
        TInt     -> I$   fromInteger$ constToInteger c
        TInt8    -> I8$  fromInteger$ constToInteger c        
        TInt16   -> I16$ fromInteger$ constToInteger c
        TInt32   -> I32$ fromInteger$ constToInteger c
        TInt64   -> I64$ fromInteger$ constToInteger c
        TWord    -> W$   fromInteger$ constToInteger c
        TWord8   -> W8$  fromInteger$ constToInteger c        
        TWord16  -> W16$ fromInteger$ constToInteger c
        TWord32  -> W32$ fromInteger$ constToInteger c
        TWord64  -> W64$ fromInteger$ constToInteger c

        TCChar   -> CC $ fromInteger$ constToInteger c
        TCUChar  -> CUC$ fromInteger$ constToInteger c
        TCSChar  -> CSC$ fromInteger$ constToInteger c
        TCShort  -> CS $ fromInteger$ constToInteger c
        TCInt    -> CI $ fromInteger$ constToInteger c
        TCLong   -> CL $ fromInteger$ constToInteger c
        TCLLong  -> CLL$ fromInteger$ constToInteger c
        TCUShort -> CUS$ fromInteger$ constToInteger c
        TCUInt   -> CUI$ fromInteger$ constToInteger c
        TCULong  -> CUL$ fromInteger$ constToInteger c
        TCULLong -> CULL$ fromInteger$ constToInteger c

        TFloat   -> F$  fromRational$ constToRational c
        TDouble  -> D$  fromRational$ constToRational c
        TCFloat  -> CF$ fromRational$ constToRational c
        TCDouble -> CD$ fromRational$ constToRational c
        
        TBool      -> err
        TChar      -> err
        TTuple _   -> err
        TArray _ _ -> err
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

