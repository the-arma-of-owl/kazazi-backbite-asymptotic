#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f run_11.sh > /dev/null; do sleep 5; done
NPROC=20 python3 -I t_sec6_heavy.py conj_sample 10 4 3000 7
echo TAILDONE
