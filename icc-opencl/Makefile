

ifeq ($(GHC),)
  GHC=ghc
endif

opencl:
	$(GHC) -DENABLE_OPENCL -i../backend-kit/ --make Test.hs -o Test.exe

cilk:
	$(GHC) -i../backend-kit/ --make Test.hs -o Test.exe

test-c: 
	EMITC=1    ALLTESTS=1 ./Test.exe 

test-cilk: 
	EMITC=cilk ALLTESTS=1 ./Test.exe 

test-opencl: 
	EMITC=0 ./Test.exe 
	EMITC=0 ONEDIMTESTS=0 MULTIDIMTESTS=1 ./Test.exe 
	EMITC=0 ONEDIMTESTS=0 USETESTS=1 ./Test.exe 

