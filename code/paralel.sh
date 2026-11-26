#!/bin/bash
# Kullanım: paralel.sh <etiket> <parça_sayısı> <geng argümanları...> -- <bbconn argümanları...>
etiket=$1; shift; K=$1; shift
gargs=(); while [ "$1" != "--" ] && [ $# -gt 0 ]; do gargs+=("$1"); shift; done; shift
bargs=("$@")
out=../sonuclar/$etiket; mkdir -p $out
for ((i=0;i<K;i++)); do
  ( geng -q "${gargs[@]}" $i/$K | ./bbconn "${bargs[@]}" > $out/parca_$i.txt 2>&1 ) &
done
wait
cat $out/parca_*.txt | grep BAGLANTISIZ > $out/baglantisiz.txt
awk '/OZET/{for(i=2;i<=NF;i++){split($i,a,"="); if(a[1]=="en_cok_yol"){if(a[2]>m)m=a[2]} else s[a[1]]+=a[2]}} END{for(k in s) printf "%s=%d ", k, s[k]; printf "en_cok_yol=%d\n", m}' $out/parca_*.txt > $out/ozet.txt
echo "BITTI $etiket: $(cat $out/ozet.txt)"
