
-- | The entrypoint to an Accelerate backend based on generating sequential C code.
module Data.Array.Accelerate.C (run) where

import           Data.Array.Accelerate (Acc)
import qualified Data.Array.Accelerate.Array.Sugar as Sug
import qualified Data.Array.Accelerate.Cilk.JITRuntime as J
import           Data.Array.Accelerate.Shared.EmitC (ParMode(..))

-- | Generate and run an Accelerate computation via sequential C code.
run :: Sug.Arrays a => Acc a -> a
run = J.run Sequential
