#!/bin/bash

./install_svf.sh
make -C passes

cd bin && clang -c ../aflpp-link-safe.c
