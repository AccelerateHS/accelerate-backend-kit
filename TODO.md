

These should go into github issues 
======================================================

 * types like Type, Prim, Const should probably be reexported by GPUIR
   and CLike IRs so that those modules are self contained.
   
 * Need a general way of maintaining array sizes after OneDimensionalize.
   (see LowerGPUIR)

 * GPUIR needs an overhaul.  Kernel declaration probably need to be
   separate from kernel invocation (e.g. a fold will be multiple
   kernel launches).

 * The interpreters are in disarray.  It would be nice to have a fully
   functional interpreter for all three major IRs.
