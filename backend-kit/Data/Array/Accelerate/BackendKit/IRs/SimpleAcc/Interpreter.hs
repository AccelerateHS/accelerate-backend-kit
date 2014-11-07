{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | An UNFINISHED example interpreter for the simplified AST defined in "Data.Array.Accelerate.SimpleAST".
--
module Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter
       (
         -- * Main module entrypoints
         run, evalSimpleAcc,
         SimpleInterpBackend(SimpleInterpBackend),

         -- * Smaller pieces that may be useful
         evalPrim,
         evalE,
         Value(..), valToConst, unConstVal, unArrVal,
        )
       where

import qualified Data.Array.Accelerate as A
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
import Data.Typeable (Typeable)

--------------------------------------------------------------------------------

-- | A unit type just to carry a `SimpleBackend` and `Backend` instance.
data SimpleInterpBackend = SimpleInterpBackend
  deriving (Show,Eq,Ord,Read, Typeable)

instance SimpleBackend SimpleInterpBackend where
  type SimpleRemote SimpleInterpBackend = SA.AccArray
  type SimpleBlob   SimpleInterpBackend = ()
  simpleCompile SimpleInterpBackend _ _ = return ()
  simpleRunRaw SimpleInterpBackend _nm acc _ = return (evalSimpleAcc acc)

  simpleCopyToHost SimpleInterpBackend ls   = return ls
  simpleCopyToDevice SimpleInterpBackend ar = return ar
  simpleCopyToPeer SimpleInterpBackend r    = return r
  simpleWaitRemote SimpleInterpBackend _ = return ()
  simpleUseRemote SimpleInterpBackend  r = return $ S.Use r
  simpleSeparateMemorySpace SimpleInterpBackend = False
  -- simpleCompileFun1 SimpleInterpBackend =
  -- simpleRunRawFun1  SimpleInterpBackend =

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
valToConst :: Value -> Const
valToConst (ConstVal c ) = c
valToConst (TupVal ls)   = Tup $ map valToConst ls
valToConst (ArrVal a)    = error$ "cannot convert Array value to Const: "++show a

unConstVal :: Value -> Const
unConstVal (ConstVal c) = c
unConstVal _ = error "FIX ME"

unArrVal :: Value -> AccArray
unArrVal   (ArrVal v)   = v
unArrVal _ = error "FIX ME"

--------------------------------------------------------------------------------
-- Evaluation:

-- | Evaluating a complete program creates a FLAT list of arrays (of scalars) as
-- a result.  Reimposing a nested structure to the resulting tuple-of-arrays is
-- not the job of this function.
--
-- Note that the length of the list will be increased BOTH because of tuples of
-- arrays, and because of unzipping arrays of tuples.
--
-- The length of the resulting list WILL match the length of the input `Prog`'s
-- `progResults` field.
--
evalSimpleAcc :: S.Prog a -> [AccArray]
evalSimpleAcc (S.Prog {progBinds, progResults})
  | maybtrace ("[dbg] evalSimpleAcc, initial env "++ show (L.map (\(ProgBind v _ _ _)->v) progBinds)
             ++"  yielded environment: "++show (M.keys finalenv)) True
  = L.map (unArrVal . (envLookup finalenv)) (resultNames progResults)
  where
    finalenv = loop M.empty progBinds

    -- A binding simply extends an environment of values.
    loop :: M.Map Var Value -> [ProgBind a] -> M.Map AVar Value
    loop env []                                  = env
    loop env (ProgBind vr _ty _ (Left rhs)  :rst) = loop (M.insert vr (evalE env rhs) env) rst
    loop env (ProgBind vr  ty _ (Right rhs) :rst) = loop (evalA env vr ty rhs) rst

    evalA :: M.Map Var Value -> Var -> Type -> AExp -> M.Map Var Value
    evalA env atype (TArray _dim elty) aexp =
      let
          bind :: Value -> M.Map Var Value
          bind v = M.insert atype v env

          lookupArray :: Var -> AccArray
          lookupArray v = let ArrVal a = envLookup env v in a
      in
      bind $ case aexp of
        S.Vr  v         -> envLookup env v
        S.Unit e        -> case evalE env e of
                             ConstVal c -> ArrVal $ SA.replicate [] c
                             oth        -> error  $"evalSimpleAcc: expecting ConstVal input to Unit, received: "++show oth

        S.Cond e1 v1 v2 -> case evalE env e1 of
                             ConstVal (B True)  -> envLookup env v1
                             ConstVal (B False) -> envLookup env v2

        S.Use arr       -> ArrVal arr
        S.Map f a       -> ArrVal $ mapArray (evalF1 env f) (lookupArray a)
        S.Generate sh f ->
          ArrVal
            $ AccArray sh'
            $ payloadsFromList elty
            $ map (evalF1 env f) (indexSpace sh')
          where
            sh' = case evalE env sh of
                    ConstVal (I i)      -> [i]
                    ConstVal (Tup is)   -> map (\(I i) -> i) is

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
        S.ZipWith  (S.Lam2 (v1,vty1) (v2,vty2) bod) vr1 vr2  ->
          if dims1 /= dims2
          then error$"zipWith: internal error, input arrays not the same dimension: "++ show dims1 ++" "++ show dims2
          -- TODO: Handle the case where the resulting array is an array of tuples:
          else ArrVal$ AccArray dims1 final
          where
            ArrVal ((AccArray dims1 pays1)) = envLookup env vr1
            ArrVal ((AccArray dims2 pays2)) = envLookup env vr2
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
        S.Backpermute sh p a ->
          ArrVal
            $ AccArray sh'
            $ payloadsFromList elty
            $ map (\ix -> let ix' = map (fromIntegral . constToInteger) $ untuple $ evalF1 env p ix
                          in  indexArray a' ix')
                  (indexSpace sh')
          where
            a'  = lookupArray a
            sh' = case evalE env sh of
                    ConstVal (I i)      -> [i]
                    ConstVal (Tup is)   -> map (\(I i) -> i) is

        --------------------------------------------------------------------------------
        -- Shave off leftmost dim in 'sh' list
        -- (the rightmost dim in the user's (Z :. :.) expression):
        S.Fold (S.Lam2 (v1,_) (v2,_) bodE) ex avr ->
          -- trace ("FOLDING, shape "++show (innerdim:sh') ++ " lens "++
          --        show (alllens, L.group alllens) ++" arr "++show payloads++"\n") $
            case payloads of
              [] -> error "Empty payloads!"
              _  -> ArrVal (AccArray sh' payloads')
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
                   [ valToConst (innerloop lookup (innerdim * i) innerdim initacc)
                   | i <- [0..newlen] ]

                -- The innermost dim is always contiguous in memory.
                innerloop :: (Int -> Const) -> Int -> Int -> Value -> Value
                innerloop _ _ 0 acc = acc
                innerloop lookup offset count acc =
                  innerloop lookup (offset+1) (count-1) $
                   evalE (M.insert v1 acc $
                          M.insert v2 (ConstVal$ lookup offset) env)
                         bodE
        S.Index     _slcty  _ae _ex   -> error "UNFINISHED: Index"
        S.Fold1     _fn _ae           -> error "UNFINISHED: Foldl1"
        S.FoldSeg   _fn _ex _ae1 _ae2 -> error "UNFINISHED: FoldSeg"
        S.Fold1Seg  _fn    _ae1 _ae2  -> error "UNFINISHED: Fold1Seg"
        S.Scanl     _fn _ex _ae       -> error "UNFINISHED: Scanl"
        S.Scanl'    _fn _ex _ae       -> error "UNFINISHED: Scanl'"
        S.Scanl1    _fn    _ae        -> error "UNFINISHED: Scanl1"
        S.Scanr     _fn _ex _ae       -> error "UNFINISHED: Scanr"
        S.Scanr'    _fn _ex _ae       -> error "UNFINISHED: Scanr'"
        S.Scanr1    _fn    _ae        -> error "UNFINISHED: Scanr1"
        S.Permute   _fn1 _ae1 _fn2 _ae2   -> error "UNFINISHED: Permute"
        S.Reshape      _ex    _ae     -> error "UNFINISHED: Reshape"
        S.Stencil      _fn  _bnd _ae  -> error "UNFINISHED: Stencil"
        S.Stencil2  _fn _bnd1 _ae1 _bnd2 _ae2 -> error "UNFINISHED: Stencil2"
        _ -> error$"Accelerate array expression breaks invariants: "++ show aexp
    
    evalA _env _atype _oth _aexp = error "FIX ME"

evalF1 :: Env -> Fun1 Exp -> Const -> Const
evalF1 env (S.Lam1 (v1,t1) body) x
  = valToConst
  $ evalE env (T.ELet (v1,t1,T.EConst x) body)

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

    T.EShapeSize sh      -> ConstVal $ I
                          $ product
                          $ map (fromIntegral . constToInteger) $ untuple $ valToConst
                          $ evalE env sh

    T.EPrimApp ty p es  -> ConstVal$ evalPrim ty p (map (valToConst . evalE env) es)

    T.ETupProject ind len ex ->
      tracePrint ("[dbg]  ETupProject: "++show ind++" "++show len++": ") $
      case (ind, len, evalE env ex) of
        (_,_,ConstVal (Tup ls)) -> ConstVal$ tuple$  slice ls
        -- TODO -- check if this makes sense ... how can we run into this kind of tuple?:
        (_ind,_,TupVal ls)      -> tupleVal$ slice ls
        (0,1,ConstVal scalar)   -> ConstVal$ scalar
        (_,_,const) -> error$ "ETupProjectFromRight: could not index "++show len++" elements at position "
                       ++ show ind ++ " in tuple " ++ show const
       where
        slice :: forall a . [a] -> [a]
        slice ls = reverse $ take len $ drop ind $ reverse ls

    -- This is our chosen representation for index values:
    T.EIndex indls       -> let ls = map (valToConst . evalE env) indls in
                          ConstVal$ tuple ls

    T.EWhile p f z      ->
      let f' x  = evalF1 env f x
          p' x  = case evalF1 env p x of
                    B b      -> b

          go x
            | p' x      = go (f' x)
            | otherwise = ConstVal x
      in
      go (valToConst $ evalE env z)

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

evalPrim _ty p [x,y] =
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

