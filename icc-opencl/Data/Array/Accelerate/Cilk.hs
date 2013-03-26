{-# LANGUAGE CPP #-}

#define MODNAME Data.Array.Accelerate.Cilk
#define BKEND CilkBackend
#define PARMODE CilkParallel
#include "C.hs"
