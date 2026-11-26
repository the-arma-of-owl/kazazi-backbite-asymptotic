# Astra Lemma 2: T = 1-2-...-k yolu + (k-2)k kenarı; i -> bağımsız W_i (boyut s_i); T kenarları -> tam iki parçalı
import sys
sys.path.insert(0, '.')
from aday import to_g6
s = list(map(int, sys.argv[1].split(',')))
k = len(s)
T = [(i, i+1) for i in range(k-1)] + [(k-3, k-1)]
start = [sum(s[:i]) for i in range(k)]
n = sum(s)
E = []
for a, b in T:
    for x in range(s[a]):
        for y in range(s[b]): E.append((start[a]+x, start[b]+y))
if len(sys.argv) > 2 and sys.argv[2] == 'g6': print(to_g6(n, E))
else:
    print(n, len(E))
    for a, b in E: print(a, b)
