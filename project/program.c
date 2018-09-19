#include <stdio.h>
#include "pop_direct_branch.c"

void scan_int(int *x)
{
    scanf("%d", x);
    return;
}

int pow2(int x)
{
    return x*x;
}

void print_int(int x)
{
    printf("%d \n", x);
    return;
}

int main ()
{
    //int a;
    //scan_int(&a);
    int p;
    p = pow2(2);
    int p1;
    p = pow2(3);
    printf("pow2 of A = ");
    print_int(p);
    return 0;
}
