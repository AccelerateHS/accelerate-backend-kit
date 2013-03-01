

module Data.Array.Accelerate.BackendKit.Phase3.FuseGenReduce (fuseGenReduce) where

import           Data.Array.Accelerate.BackendKit.IRs.GPUIR     as G
-- import           Data.Array.Accelerate.BackendKit.Utils.Helpers (genUnique, genUniqueWith, GensymM, strideName)
-- import           Data.Array.Accelerate.BackendKit.IRs.Metadata
-- import qualified Data.Array.Accelerate.BackendKit.IRs.SimpleAcc as S
-- import           Control.Applicative   ((<$>))
-- import           Control.Monad.State.Strict (runState)
-- import qualified Data.Map                        as M
-- import qualified Data.Set                        as S
-- import           Text.PrettyPrint.GenericPretty (Out(doc))


fuseGenReduce :: G.GPUProg a -> G.GPUProg a
fuseGenReduce x = x
