{-# LANGUAGE NamedFieldPuns, CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Array.Accelerate.Shared.EmitOpenCL
       (emitOpenCL)
       where

import Data.Array.Accelerate.BackendKit.IRs.SimpleAcc (Type(..), Const(..), Var)
import Data.Array.Accelerate.BackendKit.IRs.GPUIR as G
import Data.Array.Accelerate.Shared.EasyEmit as E
import Data.Array.Accelerate.Shared.EmitHelpers (emitOpenCLType)
import Data.Array.Accelerate.Shared.EmitCommon 
import Prelude as P

-- | Here is a new type just to create a new instance and implement the type class methods:
data OpenCLEmitter = OpenCLEmitter

emitOpenCL :: GPUProg () -> String
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
     body i
     -- Optional, debugging:
     -- emitStmt$ printf [stringconst "  Filled output array... out[%d] = %d\n", myind, "out" E.! myind]

  emitType _ = emitOpenCLType

  kernelReturnType _ = "__kernel void"


get_global_id :: ([Syntax] -> Syntax)
get_global_id = function "get_global_id"
