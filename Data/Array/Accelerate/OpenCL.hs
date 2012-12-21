
-- | An Accelerate backend that generates sequential C code.

module Data.Array.Accelerate.OpenCL
       (run)
       where

import Data.Array.Accelerate (Acc, Arrays)
import qualified Data.Array.Accelerate.OpenCL.JITRuntime as JIT

run :: Arrays a => Acc a -> a 
run = JIT.run JIT.OpenCL
