import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from forcing import forcing_ii, cycle_graph
import networkx as nx
n = 10
r, t, ex, nj = forcing_ii(n, cycle_graph(n), want_examples=100)
print("unreachable orderings:", len(ex))
reps = []
for P in ex:
    E = {frozenset((i, (i+1) % n)) for i in range(n)} | {frozenset((P[i], P[i+1])) for i in range(n-1)}
    G = nx.Graph([tuple(e) for e in E])
    if not any(nx.is_isomorphic(G, H) for H in reps): reps.append(G)
    adj = from_edges(n, [tuple(e) for e in E])
    paths, idx, uf, nc = r_components(n, adj)
    assert nc == 2 and comp_sizes(paths, uf) == [18, 4], (P, nc)
print("non-isomorphic graphs C10 + E(P):", len(reps), "; every one has R(G) with components [18, 4]")
