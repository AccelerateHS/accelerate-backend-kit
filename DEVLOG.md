

This is a log for development related matters
=============================================


[2012.12.23] {ghc: panic if I try --enable-tests} 
-------------------------------------------------

But "ghc --make Test.hs" works.  But "cabal install --enable-tests"
results in this error on Mac OS:

    [7 of 7] Compiling Main             ( Test.hs, dist/build/test-accelerate-cpu/test-accelerate-cpu-tmp/Main.o )
    ghc: panic! (the 'impossible' happened)
      (GHC version 7.6.1 for x86_64-apple-darwin):
	    compiler/codeGen/CgCase.lhs:572:15-61: Irrefutable pattern failed for pattern ((CoreSyn.DEFAULT,
					    deflt_absC) : others)

    Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug

On 7.4.2 (mac & linux) it works fine.

