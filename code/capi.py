# R(J) çapı: J'nin Hamilton yolları üzerinde backbite grafiğinde tüm-çiftler BFS
import sys, itertools
from collections import deque
sys.path.insert(0, '.')
from aday import edges
def ham_paths(n, adj):
    res = []
    def dfs(path, used):
        if len(path) == n:
            if path[0] < path[-1]: res.append(tuple(path))
            return
        for w in adj[path[-1]]:
            if not used >> w & 1:
                path.append(w); dfs(path, used | 1 << w); path.pop()
    for s in range(n): dfs([s], 1 << s)
    return res
def canon(p): return p if p[0] < p[-1] else p[::-1]
def nbrs(p, adjs):
    n = len(p); out = []
    for q in (p, p[::-1]):
        for k in range(2, n):
            if q[k] in adjs[q[0]]: out.append(canon(q[k-1::-1] + q[k:]))
    return out
name = sys.argv[1]
for n in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
    E = edges(name, n); adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    adjs = [set(x) for x in adj]
    P = ham_paths(n, adj); idx = {p: i for i, p in enumerate(P)}
    G = [[idx[q] for q in nbrs(p, adjs)] for p in P]
    diam = 0
    for s in range(len(P)):
        dist = [-1] * len(P); dist[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in G[x]:
                if dist[y] < 0: dist[y] = dist[x] + 1; dq.append(y)
        if min(dist) < 0: diam = float('inf'); break
        diam = max(diam, max(dist))
    print(f"{name} n={n}: yol={len(P)} çap={diam}")
