

module Data.Array.Accelerate.BackendKit.Phase2.UnzipArrays (unzipArrays) where
import Control.Monad.State.Strict
import Control.Applicative ((<$>),(<*>))
import qualified Data.Map              as M
import Debug.Trace

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
-- import Data.Array.Accelerate.BackendKit.Utils.Helpers (GensymM, genUnique, mkPrj, mapMAEWithGEnv, isTupleTy)
-- import Data.Array.Accelerate.BackendKit.CompilerUtils (shapeName)
-- import Data.Array.Accelerate.BackendKit.Phase2.NormalizeExps (wrapLets)
-- import Data.Array.Accelerate.BackendKit.IRs.Metadata (FoldStrides(..), ArraySizeEstimate(..))

-- | This pass commits to unzipped arrays.  It makes the leap between referring to
-- arrays in their zipped (array of tuples) form to their unzipped components.
-- 
-- Alas, because we are stuck with the Prog IR at this juncture, we yet can't fully
-- rewrite the AST to reflect this change..  However, after this pass the regular
-- variable fields of array op `ProgBinds` are IGNORED and the REAL names are found
-- in the SubBinds decorators.
unzipArrays :: S.Prog a -> S.Prog a
unzipArrays p =
  trace "! warning - finish unzipArrays" p
  

