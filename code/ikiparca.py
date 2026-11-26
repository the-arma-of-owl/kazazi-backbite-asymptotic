# K_{A,B} (|A|=a, |B|=b) + A içinde keyfi graf X (geng'den, a tepe). graph6 üretir.
import sys, subprocess
sys.path.insert(0, '.')
from aday import to_g6
a, b = int(sys.argv[1]), int(sys.argv[2])
out = subprocess.run(['geng', '-q', str(a)], capture_output=True, text=True).stdout.split()
for g in out:
    data = [ord(c) - 63 for c in g]; n0 = data[0]; bits = []
    for d in data[1:]:
        for i in range(5, -1, -1): bits.append((d >> i) & 1)
    E = []; k = 0
    for j in range(1, n0):
        for i in range(j):
            if bits[k]: E.append((i, j))
            k += 1
    E += [(i, a + j) for i in range(a) for j in range(b)]
    print(to_g6(a + b, E))
