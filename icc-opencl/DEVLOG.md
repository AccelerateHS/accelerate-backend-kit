

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



[2013.03.01] {Debugging Cilk backend}
-------------------------------------

The C backend is passing 63/67 (all but known-unsupported foldseg
tests and the one mysterious one).  Actually, I'm going to disable
those for the moment.  There.  63/64.


[2013.03.06] {More Debugging Cilk backend}
------------------------------------------

I'm seeing nondeterministic segfaults.  Sometimes the Cilk backend
passes all but 9/64 tests, other times it segfaults in the middle.
I just watched it segfault on p16a, and p10e.

But then if I do "rep 100" on p10e (or p16a), it completes with no
problem.  It seems like the issue relates not to running one
individual tests, but with running a whole series of tests from one
executable.  

Maybe it's leaking something with respect to the dynamically loaded
libraries?  I'm not seeing how, because it uses withDL.  Further, the
sequential C backend runs just as many tests and it never segfaults.

Presently, in addition to the mystery failure on p12, these tests are
failing due to vectorization problems:

 * p2bb, p2b, p2cc, p2ce, p2g, p2h, p2i, p2d (8 tests)
 
Starting with p2b:
  This test is nothing but one replicate on a generate.
  
Ok, the basic problem is int64s (unsupported data type).  It seems
like ICC cannot fail gracefully in this case.  In this case would be
perfectly happy if I could have a __declspec(vector) fail to vectorize
but still compile.

[2014.02.12] {Segfaults may actually be a Cilk bug}
----------------------------------------------------

I doubt Cilk gets used much in this repeated-dlopen-mode.  I started
seeing this error:

   "Cilk runtime error: thread creation (3) failed: 11" #4 

For which I filed issue #4:
   
   https://github.com/AccelerateHS/accelerate-backend-kit/issues/4



[2014.02.23] {New Policy: keep unit arrays around}
----------------------------------------

Previously we were trying to just completely git rid of arrays of
unit, with the idea that they don't need to be represented at runtime.
(Not quite true... there's still the matter of exception semantics.)

Now, I've backpedaled on that decission and started making unit arrays
real.  However, there are still places in the code I haven't managed
to fix yet, and I'm seeing the following 5 new test failures:

    run test 12/67 p11:: [Failed]
    ERROR: repackAcc2: ran out of input arrays.

    run test 13/67 p11b:: [Failed]
    ERROR: repackAcc2: ran out of input arrays.

    run test 14/67 p11c:: [Failed]
    ERROR: repackAcc2: ran out of input arrays.

    run test 23/67 p13j:: [Failed]
    ERROR: packArray: given a AccArray of the wrong type, expected Int received 2 payloads:
    ArrayPayloadUnit 1
    ArrayPayloadInt (array (0,0) [(0,-5764607523034234880)])

     dimension: []

    run test 64/67 p5:: [Failed]
    ERROR: packArray: given a AccArray of the wrong type, expected Int received 3 payloads:
    ArrayPayloadUnit 1
    ArrayPayloadInt (array (0,0) [(0,-6917529027641081856)])
    ArrayPayloadUnit 1
