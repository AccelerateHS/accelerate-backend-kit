#include "stdlib.h"
#include "stdio.h"
#include "stdint.h"
#include "stdbool.h"
void kernelFun_evt8(int flatidx0, int* tmp_1);
void kernelFun_evt8(int flatidx0, int* tmp_1)
{
    int gensym_3;
    int idx1D1;
    int idx1D2;
    int v2;
    int v4;
    int v5;
    idx1D1 = flatidx0;
    idx1D2 = (int)(0);
    v2 = idx1D1;
    v4 = v2;
    v5 = v4;
    gensym_3 = (int)(v4 * v5);
    tmp_1[flatidx0] = gensym_3;
}
void build_evt8(int sizeArg, int* tmp_1)
{
    printf(" ** RUNNING evt8 to populate %p\n", tmp_1 );
    for (int i0 = 0; (i0 < sizeArg); i0 = (i0 + 1))
    {
        kernelFun_evt8(i0, tmp_1);
    }
}
void build_evt9(int inSize, int inStride, int* tmp_0, int* tmp_1, 
                int v05)
{
    // Fold loop, reduction variable(s): [(v05,Default,TInt)]
    for (int i0 = 0; (i0 < inSize); i0 = (i0 + inStride))
    {
        int v16 = tmp_1[i0];
        int gensym_7;
        gensym_7 = (int)(v05 + v16);
        fprintf(stderr, 
                " ** Folding in position %d (it was %d) intermediate result %d\n", 
                i0, tmp_1[i0], gensym_7);
        v05 = gensym_7;
    }
    tmp_0[0] = v05;
}

int main() 
{
    // First we EXECUTE the program by executing each array op in order:
    int* tmp_1 = malloc(((sizeof(int)) * (int)(10)));
    build_evt8(10, tmp_1);
    int gensym_4;
    gensym_4 = (int)(0);
    int* tmp_0 = malloc(((sizeof(int)) * 1));
    build_evt9(10, 1, tmp_0, tmp_1, gensym_4);
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
