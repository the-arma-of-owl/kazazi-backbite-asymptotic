#!/bin/bash
cd "$(dirname "$0")"
export NPROC=18
python3 -I t_sec6_heavy.py conj 9 5 direct
for n in 5 6 7 8 9; do python3 -I t_sec6_heavy.py ore $n; done
python3 -I t_sec6_heavy.py rb 8 3
python3 -I t_sec6_heavy.py rb 9 4
python3 -I t_sec6_heavy.py rb 6 3
python3 -I t_sec6_heavy.py rb 5 3
python3 -I t_sec6_heavy.py rb 4 2
python3 -I t_sec6_heavy.py closure 7 0
python3 -I t_sec6_heavy.py closure 7 1
python3 -I t_sec6_heavy.py closure 8 1
python3 -I t_sec6_heavy.py closure 6 0
python3 -I t_sec6_heavy.py closure 6 1
python3 -I t_sec6_heavy.py closure 8 0
python3 -I t_sec6_heavy.py conj 10 5
python3 -I t_sec6_heavy.py conj 9 3
echo ALLDONE
