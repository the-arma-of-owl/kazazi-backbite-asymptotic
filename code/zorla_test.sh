#!/bin/bash
for spec in "$@"; do
  set -- $spec
  r=$(python3 -I aday.py $1 $2 g6 | ./bbconn | grep -o "baglantisiz=[0-9]*")
  t0=$(date +%s)
  s=$(python3 -I aday.py $1 $2 | ./forcing | head -2 | tr '\n' ' ')
  echo "$1 n=$2: R(J) $r | $s | $(( $(date +%s) - t0 ))s"
done
