import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
for line in open('../../data/closure_n9.txt'):
    f = line.split()
    g6 = f[1]; u = int(f[2][2:]); v = int(f[3][2:])
    n, adj = g6_decode(g6)
    assert not adj[u] >> v & 1
    _, _, ufG, ncG = r_components(n, adj)
    pG, _, _, _ = r_components(n, adj)
    a2 = adj[:]; a2[u] |= 1 << v; a2[v] |= 1 << u
    p2, _, _, nc2 = r_components(n, a2)
    print(g6, "u,v=", u, v, "d(u)+d(v)=", deg(adj, u) + deg(adj, v), "delta(G)=", min(deg(adj, x) for x in range(n)),
          "#HP(G)=", len(pG), "comps R(G)=", ncG, "| #HP(G+uv)=", len(p2), "comps R(G+uv)=", nc2)
