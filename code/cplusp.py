# Her ulaşılamayan P için G = C_n ∪ E(P) grafının graph6 kodunu yaz
import sys
sys.path.insert(0, '.')
from aday import to_g6
for line in open(sys.argv[1]):
    if not line.startswith('ornek_ulasilamayan:'): continue
    p = list(map(int, line.split(':')[1].split()))
    n = len(p)
    E = set()
    for i in range(n): E.add((min(i,(i+1)%n), max(i,(i+1)%n)))
    for a, b in zip(p, p[1:]): E.add((min(a,b), max(a,b)))
    print(to_g6(n, sorted(E)))
