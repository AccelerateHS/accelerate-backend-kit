

These should go into github issues 
======================================================

 * types like Type, Prim, Const should probably be reexported by GPUIR
   and CLike IRs so that those modules are self contained.
   
 * Need a general way of maintaining array sizes after OneDimensionalize.
   (see LowerGPUIR)

   -- starting to add a sizeEnv parameter.

 * Need a way of maintaining fold strides/dimensions after
   OneDimensionalize and into GPUIR.

 * GPUIR needs an overhaul.  Kernel declaration probably need to be
   separate from kernel invocation (e.g. a fold will be multiple
   kernel launches), and kernels need to have local work size as well
   as global.
   
   X Also should add an explicit type for Trivials.

 * The interpreters are in disarray.  It would be nice to have a fully
   functional interpreter for all three major IRs.


 * Factor out the pass that gathers sizeEnv to BEFORE ToCLike.hs
   This will ameliorate some phase ordering pain within that pass.

   
 * We need to track Fold strides between the end of OneDimensionalize
   until the conversion to GPUIR.  
