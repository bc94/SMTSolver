#!/bin/bash

BM_PATH="../xml_tc2017"
FILES=46366
VER="indexed"

for ((i=45525;i<=FILES;i++)); do
    if [ $i != 42782 ]
    then
        echo "$i"
        echo -n "$i " >> results.txt | ./run_solver.native "$BM_PATH/$i.xml" "$VER" >> results.txt 2>> error.txt
    fi
done
