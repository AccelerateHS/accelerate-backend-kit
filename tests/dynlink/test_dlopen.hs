
import Control.Exception
import System.Process
import System.Posix.DynamicLinker
import Foreign.Ptr
import Foreign.Marshal.Alloc
import Foreign.Storable
import Foreign.C.Types

main = do
  let cmd = "gcc -fpic -std=c99 gen_code.c -o gen_code.so"
  putStrLn$ "Build a shared library:  "++ cmd
  system cmd

  dl <- dlopen  "gen_code.so" [RTLD_LOCAL,RTLD_LAZY]
  putStrLn$ "Got it open..."

  ev8 <- dlsym dl "build_evt8"
  ev9 <- dlsym dl "build_evt9"

  putStrLn$ "Got evt8 function pointer: "++show ev8
  let fn = mkEv8Stub ev8
  evaluate fn
  putStrLn$ "Made dynamic stub..."
  
  tmp_1 <- mallocBytes$ (sizeOf (0::CInt)) * 10 
  putStrLn$ "Malloc'd array array at: "++ show tmp_1

  inits <- mapM (peekElemOff tmp_1) [0..9]
  putStrLn$ "Initial state of array: "++ show inits

  res <- fn 10 (tmp_1 :: Ptr CInt)
  putStrLn$ "Ran ev8 stub: "++show res

  fins <- mapM (peekElemOff tmp_1) [0..9]
  putStrLn$ "Final state of tmp_1 array: "++ show fins

  tmp_0 <- mallocBytes$ (sizeOf (0::CInt)) * 1
  _ <- (mkEv9Stub ev9) 10 1 tmp_0 tmp_1 0

  res <- peekElemOff (tmp_0 :: Ptr CInt) 0 
  putStrLn$ " Final result of reduction "++ show res
    -- int* tmp_0 = malloc(((sizeof(int)) * 1));
--    build_evt9(10, 1, tmp_0, tmp_1, gensym_4);  

  return ()

-- A stub for evt8... but what if we don't know the full args?
type Ev8 = CInt -> Ptr CInt -> IO ()
foreign import ccall "dynamic" 
   mkEv8Stub :: FunPtr Ev8 -> Ev8

type Ev9 = CInt -> CInt -> Ptr CInt -> Ptr CInt -> CInt -> IO ()
foreign import ccall "dynamic" 
   mkEv9Stub :: FunPtr Ev9 -> Ev9
