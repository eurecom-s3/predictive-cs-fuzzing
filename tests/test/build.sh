#!/bin/bash

set -e
set -x

ROOT_DIR="../.."

# setup llvm env variables
if [ -z "${LLVM_DIR}" ]; then 

  echo "[ ] retrieving the LLVM directory..."

  if [ -z "${LLVM_CONFIG}" ]; then 
      export LLVM_CONFIG='llvm-config'
  fi

  export LLVM_VER="$($LLVM_CONFIG --version 2>/dev/null | sed 's/git//')"
  if [ "$LLVM_VER" = "" ]; then
    echo "[!] llvm-config not found!"
    exit 1
  fi

  echo "[+] using LLVM $LLVM_VER"

  export PATH="$($LLVM_CONFIG --bindir)/bin:$SVF_HOME/Debug-build/bin:$PATH"
  export LLVM_DIR="$($LLVM_CONFIG --prefix)"

else

  export PATH="$LLVM_DIR/bin:$SVF_HOME/Debug-build/bin:$PATH"

fi

echo "[+] the LLVM directory is $LLVM_DIR"
export LLVM_COMPILER_PATH=$LLVM_DIR/bin

DIR=`pwd`
cd $ROOT_DIR/passes
make install || exit 1
cd $DIR

export LLVM_BITCODE_GENERATION_FLAGS="-flto"
BENCH="target"

"$LLVM_COMPILER_PATH/clang" -O1 -flto -g -c -o $BENCH.base.bc $BENCH.c
"$LLVM_COMPILER_PATH/llvm-link" -o $BENCH.linked.bc $BENCH.base.bc
../opt -dump-call-tree -call-tree-start="main" -dump-tree-file='call-tree.log' -o /dev/null $BENCH.linked.bc
../opt -internalize -internalize-public-api-file='call-tree.log' -globaldce -o $BENCH.linked_int.bc $BENCH.linked.bc
../opt -cgc-planner -cgc-strategy=params -cgc-funcs='main' -stat=0 -cgc-calls-treshold=1000000 -func-stats -dump-weights -dump-weights-root='main' -cgc -cgc-clone-prefix='' -cgc-fill=1 -dump-call-tree -call-tree-start="main" -dump-tree-file='call-tree.log' -o $BENCH.cgc0.bc $BENCH.linked_int.bc
../opt -internalize -internalize-public-api-file='call-tree.log' -globaldce -o $BENCH.cgc.bc $BENCH.cgc0.bc
# ../opt -func-stats $BENCH.linked_int.bc -o /dev/null
# ../opt -func-stats $BENCH.cgc.bc -o /dev/null

"$LLVM_COMPILER_PATH/clang++" -O1 ../driver.cc $BENCH.cgc.bc -o $BENCH.out 
