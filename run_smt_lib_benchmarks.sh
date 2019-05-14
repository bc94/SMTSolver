#!/bin/bash

VER="twl"

#ulimit -s 1000000
for file in ../smt_lib/*.smt2; do
    echo "$(basename "$file")"
    echo -n "$(basename "$file") " >> results_twl_smt2.txt | timeout 3m ./run_solver.native "$file" "$VER" >> results_twl_smt2.txt 2>> error_smt2.txt
done