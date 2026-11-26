#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f run_sec6.sh > /dev/null; do sleep 5; done
export NPROC=18
python3 -I t_sec6_heavy.py rb 6 3; python3 -I t_sec6_heavy.py rb 5 3; python3 -I t_sec6_heavy.py rb 4 2
python3 -I t_rb_sample.py 300
python3 -I t_skeletons.py sq:8 sq:9 sq:10
echo AFTERDONE
