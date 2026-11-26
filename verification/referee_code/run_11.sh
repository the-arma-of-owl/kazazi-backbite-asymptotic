#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f run_sec6.sh > /dev/null || pgrep -f run_after.sh > /dev/null; do sleep 5; done
NPROC=20 NPROC2=12 python3 -I t_conj11.py 11 6
echo DONE11
