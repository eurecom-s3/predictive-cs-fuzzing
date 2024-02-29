#!/bin/bash

set -e
export MAKEFLAGS="-j $(grep -c ^processor /proc/cpuinfo)"

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

#
# SVF
#
echo "[ ] preparing SVF..."

if [[ -d SVF ]]; then
  echo "[!] the SVF directory already exists"
  cd SVF
else
  git clone https://github.com/SVF-tools/SVF.git SVF
  cd SVF
  git checkout SVF-2.1
  git am -3 -k ../SVF-all.patch

  git clone https://github.com/SVF-tools/Test-Suite.git
  cd Test-Suite
  git checkout 72c679a49b943abb229fcb1844f68dff9cc7d522
  cd ..
fi

echo "[+] SVF ready"

echo "[ ] compiling SVF..."
source ./build.sh debug 

echo "[+] all done, goodbye!"
