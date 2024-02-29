# Predictive Context-sensitive Fuzzing

This repository hosts the code for the paper [Predictive Context-sensitive Fuzzing](https://www.ndss-symposium.org/ndss-paper/predictive-context-sensitive-fuzzing/) appeared at NDSS 2024.

### Getting started

Install the dependencies with:
```bash
# install the dependencies
$ apt-get update && \
apt-get install -y wget libstdc++-5-dev libtool-bin automake flex bison \
                   libglib2.0-dev libpixman-1-dev python3-setuptools unzip \
                   apt-utils apt-transport-https ca-certificates \
                   binutils

# install llvm-10
$ apt install -y lsb-release wget software-properties-common && wget https://apt.llvm.org/llvm.sh && chmod +x llvm.sh && ./llvm.sh 10

# Download and install the latest stable Go (for gllvm)
$ wget https://storage.googleapis.com/golang/getgo/installer_linux && \
    chmod +x ./installer_linux && \
    ./installer_linux
$ export PATH=$PATH:$HOME/.go/bin:/go/bin

# Download and compile afl++ of 08/2020.
$ git clone https://github.com/AFLplusplus/AFLplusplus.git ./afl && \
    cd ./afl && \
    git checkout 2e15661f184c77ac1fbb6f868c894e946cbb7f17

# Build without Python support as we don't need it.
# Set AFL_NO_X86 to skip flaky tests.
$ cd ./afl && unset CFLAGS && unset CXXFLAGS && \
    export CC=clang && export AFL_NO_X86=1 && \
    PYTHON_INCLUDE=/ make LLVM_CONFIG=llvm-config-10 && make install
    
# Build the AFL wrapper with gclang
wget https://raw.githubusercontent.com/llvm/llvm-project/5feb80e748924606531ba28c97fe65145c65372e/compiler-rt/lib/fuzzer/afl/afl_driver.cpp -O afl_driver.cpp
clang++-10 -std=c++11 -O2 -c afl_driver.cpp
ar r libAFLDriver.a afl_driver.o
gclang++ -std=c++11 -O2 -c afl_driver.cpp -o afl_driver_gclang.o
ar r libAFLDriverGclang.a afl_driver_gclang.o
```

Build the function cloning passes with:
```bash
$ export LLVM_DIR="/usr/lib/llvm-10" # or the llvm-10 path
$ ./build.sh
```

And compile a harness with the drop-in wrapper that we provide in the `bin` folder: `wrap_gclang` automatically runs the needed passes.

To set up a correct env for the build process, do the following steps (`OUT` is your build output directory, we follow the [FuzzBench envs](https://google.github.io/fuzzbench/getting-started/adding-a-new-fuzzer/#what-is-fuzzer_lib)):

```bash
export CC=./afl/afl-clang-fast
export CXX=./afl/afl-clang-fast++
export FUZZER_LIB=./afl/libAFLDriverGclang.a

export AFL_LLVM_DICT2FILE=$OUT/afl++.dict

export AFL_QUIET=1
export AFL_MAP_SIZE=2621440

export REAL_CC_PATH=$CC
export REAL_CXX_PATH=$CXX
export CC=./bin/wrap-gclang
export CXX=./bin/wrap-gclang++

export LLVM_BITCODE_GENERATION_FLAGS=-flto
export WLLVM_OUTPUT_LEVEL=ERROR
```

You can tune the env `CGC_STRATEGY` to change prioritization strategy (default is dataflow) and `CGC_MAXMAP` to enlarge the max map size.

Now you can compile your target simply using CC/CXX and link with:

```bash
$CXX yourfiles.o[...] $FUZZER_LIB -o youroutput.bin
```

If you want sanitization, we suggest adding `-O1 -fsanitize=address -fsanitize=array-bounds,bool,builtin,enum,float-divide-by-zero,function,integer-divide-by-zero,null,object-size,return,returns-nonnull-attribute,shift,signed-integer-overflow,unreachable,vla-bound,vptr`.

The last step is just to [fuzz with AFL++](https://github.com/AFLplusplus/AFLplusplus/blob/stable/docs/fuzzing_in_depth.md#a-running-afl-fuzz), we suggest using a CmpLog-instrumented binary in addition.

### Cite
```
@inproceedings{pred-ctx-fuzz,
    author = {Borrello, Pietro and Fioraldi, Andrea and D'Elia, Daniele Cono and Balzarotti, Davide and Querzoni, Leonardo and Giuffrida, Cristiano},
    title = {Predictive Context-sensitive Fuzzing},
    year = {2024},
    booktitle = {Network and Distributed System Security Symposium (NDSS)}
}
```
