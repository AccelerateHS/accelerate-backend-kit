{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module contains a specialization of the generic code
-- emission structure in "Data.Array.Accelerate.Shared.EmitCommon".
-- It emits OpenCL code.
-- 
-- Unfortunately, this arrangement currently requires careful
-- management of invariants that are NOT reflected in the type system.
-- See `emitOpenCL` below and `emitC` for details.

module Data.Array.Accelerate.Shared.EmitOpenCL
       (emitOpenCL)
       where

import Data.Array.Accelerate.BackendKit.IRs.Metadata  (ArraySizeEstimate, FreeVars)
import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..), Var)
import Data.Array.Accelerate.BackendKit.IRs.GPUIR as G
import Data.Array.Accelerate.Shared.EasyEmit as E
import Data.Array.Accelerate.Shared.EmitHelpers (emitOpenCLType)
import Data.Array.Accelerate.Shared.EmitCommon 
import Prelude as P

-- | Here is a new type just to create a new instance and implement the type class methods:
data OpenCLEmitter = OpenCLEmitter

-- | The final pass in a compiler pipeline.  It emits an OpenCL
-- program.
--
-- This does not handle the full GPUProg grammar, rather it requires
-- that Kernels be the only remaining array constructs (not
-- Fold/Scan/Generate).
emitOpenCL :: GPUProg (ArraySizeEstimate,FreeVars) -> String
emitOpenCL = emitGeneric OpenCLEmitter 

-- | We fill in the OpenCL-specific code generation methods:
instance EmitBackend OpenCLEmitter where
  emitIncludes _ =
    E.emitLine "#pragma OPENCL EXTENSION cl_khr_fp64 : enable\n"

  decorateArg e (v,memloc,ty)  =
     let qual = case memloc of
                  Default  -> ""
                  Global   -> "__global "
                  Local    -> "__local "
                  Constant -> "__constant "
                  Private  -> "__private "
     in (qual +++ emitType e ty, show v)
        
  invokeKern e len body = do
     let myind  = get_global_id [0] 
     i <- tmpvarinit (emitType e TInt) myind
     -- Optional, debugging:     
     -- emitStmt$ printf [stringconst " [OpenCL_DBG] Kernel invoked, global_id[0] %d, local_id[0] %d\n", myind, get_local_id [0]]     
     body i

  emitType _ = emitOpenCLType

  kernelReturnType _ = "__kernel void"


get_global_id :: ([Syntax] -> Syntax)
get_global_id = function "get_global_id"

get_local_id :: ([Syntax] -> Syntax)
get_local_id = function "get_local_id"
