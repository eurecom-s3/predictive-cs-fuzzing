#include <stdio.h>

int glob1[8] = {0};
int glob2[8] = {0};

__attribute_noinline__ int foo(int* ptr) {
    return ptr[2] + 1;
}

__attribute_noinline__ int func1(int* ptr) {
    return foo(ptr);
}

__attribute_noinline__ int func2(int* ptr) {
    return foo(ptr);
}

__attribute_noinline__ int func3(int* ptr) {
    return foo(ptr);
}

int main(int argc, char** argv) {
    return func1(glob1) + func2(glob2) + func3(glob2);
}