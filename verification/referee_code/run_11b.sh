#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f run_tail.sh > /dev/null; do sleep 5; done
NPROC2=12 python3 -I t_conj11b.py non_square_11_6.txt
echo DONE11B
