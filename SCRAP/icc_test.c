#include "stdlib.h"
#include "stdio.h"
#include "stdint.h"
#include "stdbool.h"

#include <cilk/cilk.h>
#include <cilk/reducer.h>
#include <cilk/reducer_opadd.h>

// __attribute__(vector) 
__declspec (vector) int vec_kernelFun_evt8(int flatidx1)
{
    int gensym_5;
    int idx1D2;
    int idx1D3;
    int v2;
    int v4;
    int v5;
    idx1D2 = flatidx1;
    idx1D3 = (int)(0);
    v2 = idx1D2;
    v4 = v2;
    v5 = v4;
    gensym_5 = (int)(v4 * v5);
    return gensym_5;
}

__declspec (vector)
void kernelFun_evt8(int flatidx1, int* tmp_1)
{
    int gensym_5;
    int idx1D2;
    int idx1D3;
    int v2;
    int v4;
    int v5;
    idx1D2 = flatidx1;
    idx1D3 = (int)(0);
    v2 = idx1D2;
    v4 = v2;
    v5 = v4;
    gensym_5 = (int)(v4 * v5);
    tmp_1[flatidx1] = gensym_5;
}

void build_evt8(int sizeArg, int* tmp_1)
{
#define CILKIT
#ifdef CILKIT
    #pragma vector always
    #pragma ivdep
    // #pragma simd
    _Cilk_for (int i0 = 0; (i0 < sizeArg); i0 += 1)
#else
    #pragma simd
    for (int i0 = 0; (i0 < sizeArg); i0 += 1)
#endif
    {
#ifdef USE_ELEMENTAL
#warning DEPENDING ON ELEMENTAL FUNCTION
        // kernelFun_evt8(i0, tmp_1);
        // Elemental function:
        tmp_1[i0] = vec_kernelFun_evt8(i0);
#else
// INLINED:  This actually generates THE EXACT SAME BINARY after inlining.
	int gensym_5;
	int idx1D2;
	int idx1D3;
	int v2;
	int v4;
	int v5;
	idx1D2 = i0;
	idx1D3 = (int)(0);
	v2 = idx1D2;
	v4 = v2;
	v5 = v4;
	gensym_5 = (int)(v4 * v5);
	tmp_1[i0] = gensym_5;
#endif
    }
}


void T_reduce(void* r, void* left, void* right) {
   *(int*)left = *(int*)left + *(int*)right;
}
void T_identity(void* r, void* view) {
   *((int*)view) = 0;
}
void T_destroy(void* r, void* view) {}

void build_evt9(int inSize, int inStride, int* tmp_0, int* tmp_1, 
                int v0)
{
    CILK_C_DECLARE_REDUCER(int) hv =
    	CILK_C_INIT_REDUCER(T_identity, T_reduce, T_destroy, 0);
//    	CILK_C_INIT_REDUCER(T_identity, T_reduce, T_destroy);

//    CILK_C_DECLARE_REDUCER(long) hv = REDUCER_OPADD_INIT(long, 0);
//    CILK_C_DECLARE_REDUCER(long) hv = REDUCER_OPADD_INSTANCE(long, 0);
//    CILK_C_DECLARE_REDUCER(long) hv = REDUCER_OPADD_TYPE(long)(0);

    fprintf(stderr," * View initialized: %d\n", REDUCER_VIEW(hv));

    CILK_C_REGISTER_REDUCER(hv);
    fprintf(stderr," * Reducer registered, now looping...\n");

    // Fold loop, reduction variable(s): [(v0,Default,TInt)]
#if 1
//    #pragma vector always
//    #pragma ivdep
    _Cilk_for (int i0 = 0; (i0 < inSize); i0 += inStride)
#else
    #pragma simd
    for (int i0 = 0; (i0 < inSize); i0 += inStride)
#endif
    {
        int v1 = tmp_1[i0];
//        int gensym_6;
//        gensym_6 = (int)(v0 + v1);
//        v0 = gensym_6;

        /* if (0) */
        /* fprintf(stderr, */
        /*         " ** Folding in position %d (it was %d) intermediate result \n", */
        /*         i0, tmp_1[i0]); */

        REDUCER_VIEW(hv) += v1;
    }

    fprintf(stderr," * Out of loop, now save final view\n");
    tmp_0[0] = REDUCER_VIEW(hv);
    fprintf(stderr," * Final view was %d \n", tmp_0[0]);
    CILK_C_UNREGISTER_REDUCER(hv);
    fprintf(stderr," * Reducer unregistered... \n", tmp_0[0]);
//    tmp_0[0] = v0;
}

#define SIZE 500000000
// 200 - 2646700
// 2000 -1630300296
// 111000000 - -219496032

int main() 
{
    // First we EXECUTE the program by executing each array op in order:
    int gensym_12;
    {   int gensym_4;
        int gensym_0;
        gensym_0 = (int)(SIZE);
        gensym_4 = gensym_0;
        gensym_12 = gensym_4;
    }
    fprintf(stderr, " [dbg] Top lvl scalar binding: gensym_12 = %d\n", 
            gensym_12);
    int* tmp_1 = malloc(((sizeof(int)) * gensym_12));
    build_evt8(gensym_12, tmp_1);
    int gensym_10;
    {   int gensym_7;
        gensym_7 = (int)(0);
        gensym_10 = gensym_7;
    }
    fprintf(stderr, " [dbg] Top lvl scalar binding: gensym_10 = %d\n", 
            gensym_10);
    int* tmp_0 = malloc(((sizeof(int)) * 1));
    build_evt9(SIZE, 1, tmp_0, tmp_1, gensym_10);
    // This code prints the final result(s):
    int eetmp0;
    eetmp0 = 1;
    printf(" [ ");
    printf("%d", tmp_0[0]);
    for (int i1 = 1; (i1 < eetmp0); i1 = (i1 + 1))
    {
        printf(", ");
        printf("%d", tmp_0[i1]);
    }
    printf(" ] ");
    return 0;
}
