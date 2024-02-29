#!/bin/bash

set -e
set -x

ROOT_DIR="."

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
make clean install || exit 1
cd $DIR
