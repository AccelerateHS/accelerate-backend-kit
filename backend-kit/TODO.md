

These should go into github issues 
======================================================

 * Add a TupleSize variant to ArraySizeEstimate to deal with Scanl'.
   (Or just get rid of Scanl/r'!!)

 * FreeVars should somehow be attached to specific Lambdas, not to
   array ops.

 * types like Type, Prim, Const should probably be reexported by GPUIR
   and CLike IRs so that those modules are self contained.
   
 * GPUIR needs an overhaul.  Kernel declaration probably need to be
   separate from kernel invocation (e.g. a fold will be multiple
   kernel launches), and kernels need to have local work size as well
   as global.

 * The interpreters are in disarray.  It would be nice to have a fully
   functional interpreter for all three major IRs.

 * UnzipETups: really needs to use maybeLet

 * (BUG) p20* was exposing a bug where a singleton ETuple would appear
   out of OneDimensionalize.
   
 * Need to track the FULL SHAPE of any progResults for reconstructing
   the final thing.  (Fix OneDimensionalize & downstream)
   -- ?? Is this still relevant? [2013.03.03]

 * FuseGenReduce: inline Cond's as well.
 
 * InlineCheap should inline Use dereferences.
 
