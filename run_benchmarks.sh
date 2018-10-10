#!/bin/bash

BM_PATH="../xml_tc2017"
FILES=46366
VER="twl"

for ((i=1; i<=FILES;i++)); do
    echo "$i"
    echo -n "$i " >> results.txt | ./run_solver.native "$BM_PATH/$i.xml" "$VER" >> results.txt 2>> error.txt
done