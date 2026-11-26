#!/bin/bash
# fr_par.sh <etiket> <parça> <geng argümanları...>
et=$1; shift; K=$1; shift; out=../sonuclar/fr_$et; mkdir -p $out
for ((i=0;i<K;i++)); do ( geng -q "$@" $i/$K | ./sabituc > $out/p_$i.txt 2>&1 ) & done; wait
grep -h SABIT_UC_BAGLANTISIZ $out/p_*.txt | head -20 > $out/kotu.txt
awk '/OZET/{for(i=2;i<=NF;i++){split($i,a,"="); s[a[1]]+=a[2]}} END{for(k in s) printf "%s=%d ", k, s[k]; print ""}' $out/p_*.txt > $out/ozet.txt
echo "BITTI $et: $(cat $out/ozet.txt)"
