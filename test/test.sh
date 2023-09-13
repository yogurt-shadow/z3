# !/bin/bash
rm -rf result
mkdir result
for file in `ls ./problem`
do
    ../build/z3 $(realpath "./problem/$file") -st > "result/$file.txt" 2>&1
done
