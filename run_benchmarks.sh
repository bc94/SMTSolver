#!/bin/bash

BM_PATH="../xml_tc2017"
FILES=46366
VER="indexed"

for ((i=1;i<=FILES;i++)); do
    if [ "$i" -eq 5881 -o "$i" -eq 5889 -o "$i" -eq 5899 -o "$i" -eq 5905 -o "$i" -eq 5909 -o "$i" -eq 5916 -o "$i" -eq 5919 -o "$i" -eq 5922 -o "$i" -eq 7685 -o "$i" -eq 9668 -o "$i" -eq 9673 -o "$i" -eq 9680 -o "$i" -eq 9684 -o "$i" -eq 9690 -o "$i" -eq 9695 -o "$i" -eq 9698 -o "$i" -eq 37229 -o "$i" -eq 37232 -o "$i" -eq 37256 -o "$i" -eq 37258 -o "$i" -eq 38691 -o "$i" -eq 38692 -o "$i" -eq 38729 -o "$i" -eq 38734 -o "$i" -eq 38744 -o "$i" -eq 38745 -o "$i" -eq 38746 -o "$i" -eq 38747 -o "$i" -eq 38748 -o "$i" -eq 38749 -o "$i" -eq 38750 -o "$i" -eq 39421 -o "$i" -eq 39422 -o "$i" -eq 39752 -o "$i" -eq 40500 -o "$i" -eq 40724 -o "$i" -eq 40844 ]
    then echo " "
    else 
        echo "$i"
        echo -n "$i " >> results_indexed.txt | timeout 3m ./run_solver.native "$BM_PATH/$i.xml" "$VER" >> results_indexed.txt 2>> error.txt
    fi
done
