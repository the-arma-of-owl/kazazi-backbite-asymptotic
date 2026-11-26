#!/bin/bash
# Kullanım: kapanis_par.sh <n> <k_kodu> <parça>
n=$1; k=$2; K=$3; out=../sonuclar/kapanis_n${n}_k${k}; mkdir -p $out
for ((i=0;i<K;i++)); do ( geng -q -c $n $i/$K | ./bbconn -k $k > $out/p_$i.txt 2>&1 ) & done
wait
grep -h "GERI_IHLAL" $out/p_*.txt > $out/geri.txt
awk '/KAPANIS_OZET/{for(i=2;i<=NF;i++){split($i,a,"="); s[a[1]]+=a[2]}} END{for(k in s) printf "%s=%d ", k, s[k]; print ""}' $out/p_*.txt > $out/ozet.txt
echo "BITTI n=$n k=$k: $(cat $out/ozet.txt)"
