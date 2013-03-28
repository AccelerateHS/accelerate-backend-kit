{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | The JIT defined in this module responds to the following ENVIRONMENT VARIABLES:
-- 
--  * SIMPLEINTERP=1 -- use SimpleInterp as backend INSTEAD of C/OpenCL
--  * PICKCPU=0      -- Prefer a CPU OpenCL device rather than picking the first GPU one.

module Data.Array.Accelerate.OpenCL.JITRuntime (run, rawRunIO) where 

-- Import generic third party libraries:
import qualified Control.Exception                 as E
import           Control.Monad    (forM, forM_, unless, foldM)
import           Control.Parallel.OpenCL
import           Control.Monad.State.Strict (runState)
import           Data.Array.Unsafe (unsafeFreeze, unsafeForeignPtrToStorableArray)
import           Data.Array.Unboxed                as U
import qualified Data.Array.Storable               as SA
import qualified Data.Map                          as M
import qualified Data.Set                          as Set
import           Data.List                         as L
import qualified Data.Typeable                     as T
import           Data.List.Split  (chunksOf)
import           Data.Maybe       (mapMaybe)
import           Data.Char        (isAlphaNum)
import           Foreign ( castPtr, nullPtr, Ptr )
import           Foreign.Marshal.Alloc(mallocBytes)
import           Foreign.ForeignPtr (newForeignPtr_)
import           Foreign.Storable (Storable)
import           System.IO.Unsafe (unsafePerformIO)
import           System.IO        (hPutStrLn, stderr, stdout, hFlush)
import           System.Posix.Env (getEnv)
import           System.Process   (system)
import           System.Exit      (ExitCode(..))
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Prelude hiding (log)

-- Import other compiler pieces:
import qualified Data.Array.Accelerate             as A
import qualified Data.Array.Accelerate.Array.Sugar as Sug

import           Data.Array.Accelerate.BackendKit.IRs.Metadata     (ArraySizeEstimate(..), FreeVars(..))
import           Data.Array.Accelerate.BackendKit.Utils.Helpers    (dbg,maybtrace)
import           Data.Array.Accelerate.BackendKit.CompilerPipeline (phase0, phase1, phase2, phase3, repackAcc)
import           Data.Array.Accelerate.BackendKit.SimpleArray      (payloadToPtr)
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc.Interpreter (Value(..))
import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc   as S
import           Data.Array.Accelerate.BackendKit.IRs.SimpleAcc
                     (Type(..), Const(..), AccArray(..), ArrayPayload(..), Var, typeByteSize)

import qualified Data.Array.Accelerate.BackendKit.IRs.CLike as LL
import           Data.Array.Accelerate.BackendKit.IRs.GPUIR as G
import           Data.Array.Accelerate.BackendKit.CompilerUtils (shapeName)
import           Data.Array.Accelerate.Shared.EmitHelpers       (builderName, fragileZip)
import           Data.Array.Accelerate.BackendKit.IRs.GPUIR.Interpreter (evalScalarBlock, evalExp)

import           Data.Array.Accelerate.Shared.EmitC             (emitC)
import           Data.Array.Accelerate.Shared.EmitOpenCL        (emitOpenCL)

--------------------------------------------------------------------------------
-- Main Entrypoints
--------------------------------------------------------------------------------


-- | Run an Accelerate computation using the OpenCL backend with
--   default (arbitrary) device choice.
run :: forall a . Sug.Arrays a => A.Acc a -> a
run acc =
  maybtrace ("[JIT] Repacking AccArray(s): "++show arrays) $ 
  repackAcc acc arrays
 where
   -- TODO we need a way to reimpose multidimensionality here for this
   -- full "run" interface to work properly.  The LLIR should probably
   -- track the final shape.
--   TArray dim _ = S.progType simple
   simple = phase1$ phase0 acc
   arrays = unsafePerformIO $
            rawRunIO "" simple

-- | The raw run function operating on the simplified input and output
-- types---without the extra Accelerate sugar.
rawRunIO :: String -> S.Prog () -> IO [AccArray]
rawRunIO name prog = do
  let prog' = compilerBackend prog

  useInterp <- getEnv "SIMPLEINTERP"
  case useInterp of
    Just x | x /= "" && x /= "0" ->
--      return$ evalSimpleAST (fmap (const ()) prog')
      error$"JIT.hs: Need to revive the interpreter here.."
    _ -> do 
      (ptrs,bufMap) <- setupAndRunProg name prog'
      let res = [ let BufEntry{fullshape,arraytype} = bufMap !@ vr in
                  recoverArrays fullshape arraytype ptr
                | vr  <- G.progResults prog'
                | ptr <- ptrs ]
      dbgPrint$ "[JIT] Recovered result arrays: "++ show (doc res)
      return res

-- | Compile down to the penultimate step, right before code generation.
compilerBackend :: S.Prog () -> G.GPUProg (FreeVars)
compilerBackend = phase3 . phase2 


--------------------------------------------------------------------------------
-- | Run a compiled program via C or OpenCL.  In the latter case
-- return a pointer to the result(s) in host (CPU) memory.
setupAndRunProg :: String ->
                   G.GPUProg (FreeVars) ->
                   IO ([Ptr ()], M.Map Var BufEntry)

setupAndRunProg name prog2 = do
  let progsrc  = emitOpenCL prog2
  writeFile ".accelerate_generated.cl" progsrc
  writeFile (".accelerate_generated_"++stripFileName name++".cl") progsrc
        
  -- initialize OpenCL:
  (platform:_) <- clGetPlatformIDs
  devs   <- clGetDeviceIDs platform CL_DEVICE_TYPE_ALL
  devNames <- mapM clGetDeviceName devs  
  dbgPrint$ "[JIT] Found devices: "++show devNames
  devtys <- mapM clGetDeviceType devs

  pickCPU <- getEnv "PICKCPU"
      -- HACK -- EQ instance is missing for CL_DEVICE_TYPE_GPU:
  let isGPU (_,tys)  = "CL_DEVICE_TYPE_GPU" `elem` (map show tys)
      (prd,desired)  = case pickCPU of
                        Just x | x /= "" && x /= "0" -> ((not . isGPU), "CPU")
                        _                            -> (isGPU, "GPU")
      firstPicks     = filter prd (zip devs devtys)
  dev <- case firstPicks of
          ((h,_):_) -> do clGetDeviceName h >>= (dbgPrint . (("[JIT] Found "++desired++" (preferred), selecting: ")++))
                          return h
          _         -> do clGetDeviceName (head devs) >>= (dbgPrint . ("[JIT] Selecting device: "++))
                          return (head devs)
  dbgPrint$ "[JIT]  Device Stats: "
  dver      <- clGetDeviceVersion dev
  driver    <- clGetDeviceDriverVersion dev
  maxConst  <- clGetDeviceMaxConstantBufferSize dev
  maxAlloc  <- clGetDeviceMaxMemAllocSize dev
  memSize   <- clGetDeviceGlobalMemSize dev
  memCachSz <- clGetDeviceGlobalMemCacheSize dev
  memCachLn <- clGetDeviceGlobalMemCachelineSize dev
  maxWG     <- clGetDeviceMaxWorkGroupSize dev
  wiszs     <- clGetDeviceMaxWorkItemSizes dev
  widims    <- clGetDeviceMaxWorkItemDimensions dev
  memtype   <- clGetDeviceLocalMemType dev
  localSz   <- clGetDeviceLocalMemSize dev
  units     <- clGetDeviceMaxComputeUnits dev
  dbgPrint$ "[JIT]  * device/driver ver: "++show dver ++" "++show driver
  dbgPrint$ "[JIT]  * const  mem size : "++commaint maxConst
  dbgPrint$ "[JIT]  * local  mem type : "++show memtype
  dbgPrint$ "[JIT]  * local  mem size : "++commaint localSz  
  dbgPrint$ "[JIT]  * global mem size : "++commaint memSize
  dbgPrint$ "[JIT]  * global mem cache: "++commaint memCachSz
  dbgPrint$ "[JIT]  * global mem line : "++commaint memCachLn
  dbgPrint$ "[JIT]  * max alloc  size : "++commaint maxAlloc
  dbgPrint$ "[JIT]  * max work group size : "++commaint maxWG
  dbgPrint$ "[JIT]  * max work item sizes : "++show wiszs
  dbgPrint$ "[JIT]  * max work item dims  : "++show widims
  dbgPrint$ "[JIT]  * max compute units : "++show units

  context <- clCreateContext [CL_CONTEXT_PLATFORM platform] [dev] print

--  dbgPrint$ "[JIT] Platform and device and context: "++show (platform,dev,context)
  -- We should be able to enable out-of-order here.  But it's giving me errors [2012.09.29]:
  --  q <- clCreateCommandQueue context dev [CL_QUEUE_OUT_OF_ORDER_EXEC_MODE_ENABLE] 
  q <- clCreateCommandQueue context dev []
  -- TODO: Could do the above once, globally, rather than on each Prog execution.
  
  -- Initialize and compile program:
  program <- clCreateProgramWithSource context progsrc

  unless (isEmptyProgram progsrc) $ do 
      E.catch (clBuildProgram program [dev] "")
              (\ e -> case e of 
                       CL_BUILD_PROGRAM_FAILURE -> do
                          hPutStrLn stderr$ "\nCaught CL_BUILD_PROGRAM_FAILURE! Here's the build log: "
                          hPutStrLn stderr "============================================================"                      
                          log <- clGetProgramBuildLog program dev
                          hPutStrLn stderr log
                          hPutStrLn stderr "============================================================"                      
                       _ -> E.throw e)
      binaries <- clGetProgramBinaries program
      dbgPrint$ "[JIT] Program built, source code "++
        show (length progsrc)++" chars, binary "++show(L.map length binaries)++" bytes"

  -- With compilation finished we can launch the kernel DAG:
  (ptrs,bufMap) <- runDAG (context, q, program) prog2

  -- CLEANUP openCL:
  _ <- clReleaseCommandQueue q  
  _ <- clReleaseContext context
  _ <- clReleaseProgram program
  clUnloadCompiler  
  
  return (ptrs, bufMap)
  -- Note, we don't explicitly clean up everything above.  It gets garbage collected.

 where
   -- | HACK: detect an empty openCL program. (Currently very inefficiently)
   isEmptyProgram :: String -> Bool
   isEmptyProgram str = not (elem "__kernel" (words str))

-- | This is what we need to know about an outstanding buffer residing in OpenCL:
--
--   The CLEvent is the envent that, once completed, ensures that the
--   buffer is filled in ON THE OPENCL SIDE.  A copy to the host side
--   is still required after that point.
data BufEntry = BufEntry { logicalevt :: EvtId,
                           clmem     :: CLMem,
                           bytesize  :: Int,
                           fullshape :: [Int],
                           arraytype :: Type }
  deriving Show

----------------------------------------------------------------------------------------------------
-- | Take a program (DAG) and launch an OpenCL task graph that mimics the
--   structure of that program.  Finally, collect the results.
runDAG :: (CLContext, CLCommandQueue, CLProgram)
       -> G.GPUProg (FreeVars)
       -> IO ([Ptr ()], M.Map Var BufEntry)
runDAG (context, q, clprog) (G.GPUProg{progBinds, progResults, lastwriteTable}) = do
    dbgPrint$ "[JIT] Launching a DAG of "++show (length progBinds)++" nodes..." 
  
    doPBs M.empty M.empty M.empty progBinds
 where
   sizety :: M.Map Var ((FreeVars), Type)
   sizety = M.fromList$ L.concatMap
              (\ (G.GPUProgBind {outarrs, decor=dec} ) -> map (\ (vr,_,ty) ->  (vr,(dec,ty))) outarrs)
            progBinds

   ------------------------------------------------------------
   -- Wait until a set of arrays are computed and copy them back to the host:
   -- Depends on 'q' and 'sizety':
   waitArraysGetPtrs :: M.Map Var BufEntry -> M.Map EvtId CLEvent -> [Var] -> IO [Ptr ()]
   waitArraysGetPtrs bufMap evMap [] = return [] -- Nothing to do.
   waitArraysGetPtrs bufMap evMap arrayVars = do
     -- Now we READ all the final result buffers out:
     let bufs   = L.map (bufMap !@) arrayVars
         clevts = L.map ((evMap !@) . logicalevt) bufs
         tys    = L.map ((sizety !@)) arrayVars
     dbgPrint$ "[JIT] Waiting for arrays "++show arrayVars++
               "... logical evnts: "++ show (L.map logicalevt bufs)++ ", openCL evts: "++ show clevts
         
     _ <- clWaitForEvents clevts  -- We COULD simply do a barrier instead.
     ls <- forM (zip bufs tys) $ \ (BufEntry{logicalevt,clmem,bytesize}, (_, TArray _ _elty)) -> do
       dbgPrint$"[JIT]   Reading result array of "++show bytesize++" bytes"
       let clevt = evMap !@ logicalevt
       -- It SHOULD be possible to use MapBuffer instead of ReadBuffer because of CL_MEM_ALLOC_HOST_PTR:
       if False then        
          clEnqueueMapBuffer q clmem False [CL_MAP_READ] 0 bytesize [clevt]
        else do
          newBuf <- mallocBytes bytesize
          ev <- clEnqueueReadBuffer q clmem False 0 bytesize newBuf [clevt]
          return (ev,newBuf)

     let events2 = L.map fst ls
         ptrs    = L.map snd ls
     dbgPrint$"[JIT]   Buffer read(s) launched, waiting for them to complete..."
     _ <- clWaitForEvents events2 -- Wait for result collection
--     mapM_ clReleaseMemObject (map clmem prs) -- Once we read it we're done with it...
--     clReleaseEvent....
     return ptrs              -- Return pointers to all results.
     
   --------------------------------------------------------------------------------
   -- INVARIANT: valEnv tracks all scalar bindings but ONLY array
   --            variables which have been forced/copied to the CPU.
   -- INVARIANT: bufMap tracks in-scope array variables, but none of the scalar variables.
   -- INVARIANT: evMap binds already-launched logical events to OpenCL events
   doPBs :: M.Map Var Value
         -> M.Map Var BufEntry
         -> M.Map EvtId CLEvent
         -> [G.GPUProgBind (FreeVars)] 
         -> IO ([Ptr ()], M.Map Var BufEntry)
   doPBs _ bufMap evMap [] = do ptrs <- waitArraysGetPtrs bufMap evMap progResults
                                return (ptrs, bufMap)

   -- doPBs valEnv evMap (LLProgBind resultBinds _ (ScalarCode bk) : rest) = do
   --   return undefined

   doPBs valEnv bufMap evMap (G.GPUProgBind {evtid, evtdeps, outarrs=resultBinds, op} : rest) = 
    case op of
     ScalarCode blk ->
       -- This case alone is currently allowed to bind MULTIPLE results.
       do (vals,valEnv') <- evalTopLvlBlk valEnv blk
          let pairs = fragileZip (map fst3 resultBinds) (map ConstVal vals)
              env'  = foldr (uncurry M.insert) valEnv' pairs 
          doPBs env' bufMap evMap rest
      
     -- Every time we encounter a Use we have to move memory over:
     Use accarr@(AccArray shape payls) -> do       
       let payload = case payls of
                      [x] -> x
                      _   -> error$"JIT.hs: can only execute with arrays of scalars, got an array of tuples of "
                                   ++show (length payls)++" elements"
           ptr     = payloadToPtr payload
           bufSize = (product shape) * eltBytesize
--       mem <- clCreateBuffer context [CL_MEM_READ_ONLY, CL_MEM_USE_HOST_PTR] (bufSize, ptr)
       mem <- clCreateBuffer context [CL_MEM_READ_WRITE, CL_MEM_USE_HOST_PTR] (bufSize, ptr)           
       dbgPrint$ "[JIT] Use: host buffer "++show ptr++" (shape "++show shape++") occupies "++show bufSize
                 ++" bytes, now executing clEnqueueWriteBuffer"
       -- Copy the data over to the GPU: this could happen lazily and
       -- thereby be more PRECISE (i.e. not load too early):
       clevt <- clEnqueueWriteBuffer q mem False 0 bufSize ptr []

       let entry = BufEntry{ logicalevt = evtid
                           , clmem      = mem
                           , bytesize   = bufSize
                           , fullshape  = shape
                           , arraytype  = pbty
                           }
       -- No need to wait on copying an array back from the GPU: insert it in valEnv:
       doPBs (M.insert nm (ArrVal accarr) valEnv)
             (M.insert nm entry bufMap)
             (M.insert evtid clevt evMap)
             rest 
     
     -- TODO: Cond needs to come back to the CPU to evaluate the
     -- scalar expression.
     Cond etest v1 v2     -> do
       (val,valEnv') <- evalTopLvlExp valEnv etest
       dbgPrint$ "[JIT] Array level conditional, predicate "++show etest++" evaluated to "++show val
       let go vr = doPBs valEnv' (M.insert nm (bufMap !@ vr) bufMap)
                                 (M.insert nm (evMap !@ vr) evMap) rest
       case val of 
         ConstVal (B True)  -> go v1
         ConstVal (B False) -> go v2
         _                  -> error$"JIT.hs: bad value, condition test should return bool: "++show val


     NewArray eSz -> do
       (ConstVal (I n),valEnv') <- evalTopLvlExp valEnv eSz
       let bufSize = n * eltBytesize
       dbgPrint$ "[JIT] Creating new buffer of bytesize "++show bufSize++" ... "
       mem_out <- clCreateBuffer context [CL_MEM_READ_WRITE, CL_MEM_ALLOC_HOST_PTR] (bufSize, nullPtr)

       -- At this point we know what event we *will* have to wait for, yet the last writer to this
       -- array won't have actually run yet, so we won't have the real OpenCL event yet:
       let Just evnt = L.lookup nm lastwriteTable
       let newentry = BufEntry{ logicalevt=evnt, clmem=mem_out, 
                                bytesize=bufSize, fullshape=[n], arraytype=pbty }
       dbgPrint$ "[JIT] Adding new buffer entry to table: "++show newentry                      
       doPBs valEnv' (M.insert nm newentry bufMap) evMap rest

     ------------------------------Kernel case----------------------------------
     -- Launch a kernel of specified dimension:
     -- Handling a Kernel enqueues one GPU kernel, waiting on upstream events. 
     Kernel iters (Lam formals _bod) args ->
       do kernel <- clCreateKernel clprog (builderName evtid)
          name   <- clGetKernelFunctionName kernel
          dbgPrint$ "[JIT] kernel created: "++name
          let (_iterVs, shapeEs) = unzip iters
          -- Evaluate size expression(s) on the CPU side (interpreted):
          (valEnv', ls) <- foldM (\ (env,ls) ex -> do (val,env') <- evalTopLvlExp env ex
                                                      return (env',val:ls))
                                 (valEnv,[]) shapeEs
          let shapeIs :: [Int]
              shapeIs = map (\ (ConstVal (I n)) -> n) (reverse ls)

          dbgPrint$"[JIT] Kernel args are size followed by formals.  Size: "++ show shapeIs ++" Formals: "++show formals 
          dbgSetArg kernel 0 (product shapeIs)

          -- Set the rest of the inputs as kernel arguments:           
          forM_ (zip [1..] args) $ \ (ind, expr) -> do
            case expr of
              -- Special OpenCL convention
              EUnInitArray elt sz -> do 
                                        let bytes = typeByteSize elt * sz
                                        dbgPrint$ "[JIT]    Setting kernel "++name++" argument #"++show ind
                                                  ++" to NULL pointer for local array of size "++show bytes 
                                        clSetKernelArg kernel ind bytes nullPtr
              EVr vr -> 
                case (M.lookup vr bufMap, M.lookup vr valEnv') of 
                  (Just (BufEntry{clmem}),_) -> dbgSetArg kernel ind clmem -- an opencl-side ARRAY 
                  (Nothing, Just val) -> 
                    let err2 = error$"JIT.hs/runDag: cannot send this value to OpenCL as argument: "++show val in
                    case val of 
                      ConstVal (I    n) -> dbgSetArg kernel ind n
                      ConstVal (I8   n) -> dbgSetArg kernel ind n
                      ConstVal (I16  n) -> dbgSetArg kernel ind n
                      ConstVal (I32  n) -> dbgSetArg kernel ind n
                      ConstVal (I64  n) -> dbgSetArg kernel ind n
                      ConstVal (W    n) -> dbgSetArg kernel ind n
                      ConstVal (W8   n) -> dbgSetArg kernel ind n
                      ConstVal (W16  n) -> dbgSetArg kernel ind n
                      ConstVal (W32  n) -> dbgSetArg kernel ind n
                      ConstVal (W64  n) -> dbgSetArg kernel ind n
                      ConstVal (F    n) -> dbgSetArg kernel ind n
                      ConstVal (D    n) -> dbgSetArg kernel ind n
                      ConstVal (B    n) -> dbgSetArg kernel ind n
                      ConstVal (C    n) -> dbgSetArg kernel ind n
                      ConstVal (CF   n) -> dbgSetArg kernel ind n
                      ConstVal (CD   n) -> dbgSetArg kernel ind n
                      ConstVal (CS   n) -> dbgSetArg kernel ind n
                      ConstVal (CI   n) -> dbgSetArg kernel ind n
                      ConstVal (CL   n) -> dbgSetArg kernel ind n
                      ConstVal (CLL  n) -> dbgSetArg kernel ind n
                      ConstVal (CUS  n) -> dbgSetArg kernel ind n
                      ConstVal (CUI  n) -> dbgSetArg kernel ind n
                      ConstVal (CUL  n) -> dbgSetArg kernel ind n
                      ConstVal (CULL n) -> dbgSetArg kernel ind n
                      ConstVal (CC   n) -> dbgSetArg kernel ind n
                      ConstVal (CSC  n) -> dbgSetArg kernel ind n
                      ConstVal (CUC  n) -> dbgSetArg kernel ind n
                      ConstVal (Tup _)  -> err2
                      TupVal _          -> err2
                      ArrVal _          -> err2
                  (Nothing, Nothing) -> error$"JIT.hs/runDag: variable in neither scalar nor array list: "++show vr
                  
              _ -> error$"Jit.hs: handling Kernel.  Invariant broken, kernel arg should only be EVr or EUnInitArray, not "++show expr

                
          let allEvs    = mapMaybe (`M.lookup` evMap) evtdeps
              dims      = if []==shapeIs then [1] else shapeIs  -- Handle ONLY zero or one dim currently.
              groupDims = L.map (const 1) shapeIs
--              groupDims = dims -- TEMP: Do everything in a single workgroup for now.
          --------------------- *THE Kernel Launch* ---------------------
          clevnt <- clEnqueueNDRangeKernel q kernel dims groupDims allEvs
          -- let newentry = BufEntry{clevt=evnt, clmem=mem_out, 
          --                         bytesize=bufSize, fullshape=shapeIs, arraytype=pbty }
          kname <- clGetKernelFunctionName kernel
          dbgPrint$ "[JIT] Kernel "++kname++" LAUNCHED, ndrange "++show dims++" groupDims "++show groupDims

          -- clReleaseEvent     -- TODO, free all events when flushing out the DAG.
          -- clReleaseMemObject -- TODO, free all memobjects when flushing out the DAG.
          -- Once the kernel is enqued, it is safe for us to let go of our handle on it:
          -- clReleaseKernel kernel

          doPBs valEnv' bufMap (M.insert evtid clevnt evMap) rest 
     ----------------------------END Kernel case--------------------------------

     _ -> error$"JIT.hs: this operator is not handled at this stage: "++show (doc op)

    where
        [(nm,_,pbty)] = resultBinds -- Leveraging LAZINESS here.  Not all cases use this.  
        TArray _ elty = pbty
        eltBytesize    = typeByteSize elty

        -- | Lazily force any arrays that we need to compute the expression.  Then extend the value
        -- environement as necessary and evaluate a top level Exp.  Depends on 'evMap', 'env', and
        -- 'fvs' bound above:
        evalTopLvlExp :: M.Map Var Value -> Exp -> IO (Value, M.Map Var Value)
        evalTopLvlExp env ex = do
          let fvs = Set.toList$ expFreeVars ex 
          env' <- forceArrVals env fvs
          return (ConstVal$ evalExp env' ex, env')

        -- | Same but for blocks.
        evalTopLvlBlk :: M.Map Var Value -> ScalarBlock -> IO ([Const], M.Map Var Value)
        evalTopLvlBlk env blk = do
            let fvs = Set.toList$ scalarBlockFreeVars blk
            env2 <- forceArrVals env fvs
            let (vals,env3) = runState (evalScalarBlock blk) env2
            return (vals, env3)

        -- | Wait on array results and add those to the existing environment.
        forceArrVals :: M.Map Var Value -> [Var] -> IO (M.Map Var Value)
        forceArrVals env fvs = do
          -- First, we don't bother with anything we ALREADY have a binding for:
          let fvs' = L.filter (not . (`M.member` env)) fvs
          -- And anything we don't have a binding for had better be in evMAP:
          let (arrVs,unbound) = L.partition (`M.member` evMap) fvs'
          unless (unbound == []) $           
            error$ "JIT.hs: variable(s) not bound in valEnv OR evMap: "++show unbound
          -- FIXME: It would be nicer to read back just as much
          -- of the data as we need rather than whole arrays:
          ptrs <- waitArraysGetPtrs bufMap evMap arrVs
          let accArrays = L.zipWith (\ avr ptr -> 
                                      let (_,aty) = sizety !@ avr 
                                          BufEntry{fullshape} = bufMap !@ avr in
                                      recoverArrays fullshape aty ptr ) 
                                    arrVs ptrs
          return (M.union env
                   (M.fromList$ L.zip arrVs (L.map ArrVal accArrays)))




----------------------------------------------------------------------------------------------------

-- | Rebuild a Haskell array from a raw (CPU side) pointer.  This
--   currently involves copying, but that can be fixed.
recoverArrays :: [Int] -> Type -> Ptr () -> AccArray
-- FIXME: this needs to handle multi-payload arrays.
recoverArrays shape aty ptr = AccArray shape payload
  where
    TArray _dims ety = aty
    elms = product shape
    payload = 
     case ety of 
       TInt     -> [ArrayPayloadInt    $ fromPtr elms ptr]
       TInt8    -> [ArrayPayloadInt8   $ fromPtr elms ptr]
       TInt16   -> [ArrayPayloadInt16  $ fromPtr elms ptr]
       TInt32   -> [ArrayPayloadInt32  $ fromPtr elms ptr]
       TInt64   -> [ArrayPayloadInt64  $ fromPtr elms ptr]
       TWord    -> [ArrayPayloadWord   $ fromPtr elms ptr]
       TWord8   -> [ArrayPayloadWord8  $ fromPtr elms ptr]
       TWord16  -> [ArrayPayloadWord16 $ fromPtr elms ptr]
       TWord32  -> [ArrayPayloadWord32 $ fromPtr elms ptr]
       TWord64  -> [ArrayPayloadWord64 $ fromPtr elms ptr]
       TFloat   -> [ArrayPayloadFloat  $ fromPtr elms ptr]
       TDouble  -> [ArrayPayloadDouble $ fromPtr elms ptr]
       TChar    -> [ArrayPayloadChar   $ fromPtr elms ptr]
       TBool    -> [ArrayPayloadBool   $ fromPtr elms ptr]
   -- FINISHME -- C Types
--       TTuple tys -> concatMap (uncurry payloadsFromList)
--                               (zip tys (L.transpose $ map unTup ls))
       oth -> error$"recoverArrays: unhandled in ArrayPayload: "++show oth


-- | Retrieve a UArray from a Ptr.  This will, unfortunately, involve copying.
fromPtr :: forall a b . (IArray UArray b, Storable b)
        => Int -> Ptr a -> (U.UArray Int b)
fromPtr elms ptr = unsafePerformIO $ sa >>= unsafeFreeze 
  where
    sa :: IO (SA.StorableArray Int b)
    sa = do fp <- newForeignPtr_ (castPtr ptr)
            unsafeForeignPtrToStorableArray fp (0, elms - 1)
    

----------------------------------------------------------------------------------------------------
-- Misc Helpers:

dbgPrint :: String -> IO ()
dbgPrint str = if not dbg then return () else do
    putStrLn str
    hFlush stdout

-- | Remove exotic characters to yield a filename
stripFileName :: String -> String
stripFileName name = filter isAlphaNum name

detuple :: Const -> [Const]
detuple (Tup ls) = ls
detuple x        = [x]

-- | A map dereference with a better error message:
(!@) :: (Ord k, Show k, Show a) => M.Map k a -> k -> a
mp !@ key = case M.lookup key mp of
             Nothing -> error$"Map lookup, could not find key: "++show key
                        ++" in map:\n   "++show mp
             Just x  -> x


-- I cannot *believe* there is not a standard call or an
-- easily-findable hackage library supporting locale-based printing of
-- numbers. [2011.01.28]
commaint :: (Show a, Integral a) => a -> String
commaint n = 
   reverse $
   concat $
   intersperse "," $ 
   chunksOf 3 $ 
   reverse (show n)


fst3 :: (t, t1, t2) -> t
fst3 (a,_,_) = a

dbgSetArg :: (Show a, Storable a, T.Typeable a) => CLKernel -> CLuint -> a -> IO ()
dbgSetArg kern ind val = do
  name <- clGetKernelFunctionName kern
  dbgPrint$ "[JIT]    Setting kernel "++name++" argument #"++show ind++" to val of type "++show (T.typeOf val)++": "++show val
  clSetKernelArgSto kern ind val
