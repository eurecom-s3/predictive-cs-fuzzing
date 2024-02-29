#include <unistd.h>
#include <stdio.h>

int LLVMFuzzerTestOneInput(const __uint8_t* data, size_t size);

int main(int argc, char *argv[]) {
    __uint8_t data[1024*500];
    int ret = read(0, data, sizeof data);
    LLVMFuzzerTestOneInput(data, ret);
}