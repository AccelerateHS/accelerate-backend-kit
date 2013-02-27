

These should go into github issues 
======================================================

 * Add a TupleSize variant to ArraySizeEstimate to deal with Scanl'.
   (Or just get rid of Scanl/r'!!)

 * FreeVars should somehow be attached to specific Lambdas, not to
   array ops.

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

 * It looks like OneDimensionalize is not doing anything with USE.
   That needs to be fixed.  

 * OneDimensionalize should probably introduce _size variables to go
   long with the _shape ones.   

 * Improve UnzipETups so that it actually unzips top level ETuple
   expressions, avoiding the need for them to become ugly
   ScalarBlocks. Also, make use of simpleBlockToExp.

 * Improve OneDimensionalize to use maybeLet everywhere.
  * UnzipETups: really needs to use maybeLet

 * (BUG) p20* was exposing a bug where a singleton ETuple would appear
   out of OneDimensionalize.
   
 * Need to track the FULL SHAPE of any progResults for reconstructing
   the final thing.  (Fix OneDimensionalize & downstream)

