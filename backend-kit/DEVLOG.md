

[2013.08.19] {Ready to switch *off* SURFACE_TUPLES}

I can have an explicit tuple _flattening_ pass afterwards, but the
current strategy is not sound (it is spoofed by left-nested tuples).

At the starting point (now) the test results on my Mac are:

 * C sequential backend (gcc): 48/48
 * backend-kit (interpreter): 60/84
 * DynamicAcc: 52/110

