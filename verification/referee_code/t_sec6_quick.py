import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from collections import deque

# --- Item 3: C_10 + edges of the path 0,1,7,8,9,4,3,2,6,5
n = 10
E = [(i, (i+1) % n) for i in range(n)]
P = [0,1,7,8,9,4,3,2,6,5]
E += [(P[i], P[i+1]) for i in range(n-1)]
adj = from_edges(n, E)
print("item3: degrees", [deg(adj, v) for v in range(n)], "delta", min(deg(adj, v) for v in range(n)))
paths, idx, uf, nc = r_components(n, adj)
print("item3: #HP", len(paths), "#components", nc, "sizes", comp_sizes(paths, uf))
# Hamiltonian? C_10 is a subgraph, so yes.  Check which component contains C10-deletions
cyc = canon(tuple(range(n)))
print("item3: component size containing C10 - {9,0}:", sum(1 for i in range(len(paths)) if uf.find(i) == uf.find(idx[cyc])))
# list the 4-path component
small = [p for i, p in enumerate(paths) if uf.find(i) != uf.find(idx[cyc])]
print("item3: small component:", small)

# --- the 5 graph6 codes in hamiltonian_disconnected.txt
codes = []
for line in open('../../data/hamiltonian_disconnected.txt'):
    if line.startswith('BAGLANTISIZ'):
        codes.append(line.split()[1])
for c in codes:
    n2, adj2 = g6_decode(c)
    paths2, idx2, uf2, nc2 = r_components(n2, adj2)
    # Hamiltonian?  check a HP with adjacent endpoints
    ham = any(adj2[p[0]] >> p[-1] & 1 for p in paths2)
    print("g6", c, "n", n2, "delta", min(deg(adj2, v) for v in range(n2)), "#HP", len(paths2), "comps", nc2, comp_sizes(paths2, uf2), "hamiltonian", ham)

# --- Item 7: diameters of R(P_n^2)
def sq(n):
    E = [(i, i+1) for i in range(n-1)] + [(i, i+2) for i in range(n-2)]
    return from_edges(n, E)
diams = []
for n in range(4, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 15):
    adj = sq(n)
    paths = ham_paths(n, adj)
    idx = {p: i for i, p in enumerate(paths)}
    G = [[idx[r] for r in r_neighbours(n, adj, p)] for p in paths]
    D = 0
    for s in range(len(paths)):
        dist = [-1] * len(paths); dist[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in G[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1; dq.append(y)
        assert min(dist) >= 0
        D = max(D, max(dist))
    diams.append(D)
    print("P_n^2 n=%d #HP=%d diam=%d" % (n, len(paths), D), flush=True)
print("diameters:", diams)
