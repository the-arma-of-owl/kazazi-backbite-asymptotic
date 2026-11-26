# Independent referee library: backbites, Hamiltonian paths, R(G) components.
# Graphs: n and adjacency bitmasks adj[v] (int). Paths: tuples of vertices.
import random

def canon(p):
    return p if p[0] < p[-1] else p[::-1]

def bb_front(p, k):
    """Backbite at endpoint p[0] with target p[k] (0-indexed, k>=2).
    Adds p[0]p[k], deletes p[k-1]p[k]; result p[k-1..0] + p[k..]."""
    assert 2 <= k < len(p)
    return p[k-1::-1] + p[k:]

def bb(p, end, target):
    """Backbite at endpoint `end` (must be p[0] or p[-1]) with target vertex `target`.
    Returns the new path oriented arbitrarily, and the deleted edge."""
    q = p if p[0] == end else p[::-1]
    assert q[0] == end
    k = q.index(target)
    assert k >= 2, "target is the second vertex or the endpoint itself"
    return q[k-1::-1] + q[k:], frozenset((q[k-1], q[k]))

def edges_of_path(p):
    return {frozenset((p[i], p[i+1])) for i in range(len(p)-1)}

def is_ham_path(n, adj, p):
    if len(p) != n or len(set(p)) != n: return False
    return all(adj[p[i]] >> p[i+1] & 1 for i in range(n-1))

def ham_paths(n, adj):
    res = []
    full = (1 << n) - 1
    sys_rec = __import__('sys'); sys_rec.setrecursionlimit(10000)
    path = []
    def dfs(used, last):
        if used == full:
            if path[0] < path[-1]: res.append(tuple(path))
            return
        m = adj[last] & ~used
        while m:
            b = m & -m; w = b.bit_length() - 1; m ^= b
            path.append(w); dfs(used | b, w); path.pop()
    for s in range(n):
        path.append(s); dfs(1 << s, s); path.pop()
    return res

def r_neighbours(n, adj, p):
    out = []
    for q in (p, p[::-1]):
        am = adj[q[0]]
        for k in range(2, n):
            if am >> q[k] & 1:
                out.append(canon(q[k-1::-1] + q[k:]))
    return out

class UF:
    def __init__(self, m):
        self.p = list(range(m))
    def find(self, x):
        p = self.p
        while p[x] != x:
            p[x] = p[p[x]]; x = p[x]
        return x
    def union(self, a, b):
        a = self.find(a); b = self.find(b)
        if a != b: self.p[a] = b

def r_components(n, adj, paths=None):
    """Return (paths, idx, uf, number_of_components)."""
    if paths is None: paths = ham_paths(n, adj)
    idx = {p: i for i, p in enumerate(paths)}
    uf = UF(len(paths))
    for i, p in enumerate(paths):
        for r in r_neighbours(n, adj, p):
            uf.union(i, idx[r])
    roots = {uf.find(i) for i in range(len(paths))}
    return paths, idx, uf, len(roots)

def comp_sizes(paths, uf):
    from collections import Counter
    c = Counter(uf.find(i) for i in range(len(paths)))
    return sorted(c.values(), reverse=True)

def from_edges(n, E):
    adj = [0] * n
    for a, b in E:
        if a != b:
            adj[a] |= 1 << b; adj[b] |= 1 << a
    return adj

def deg(adj, v):
    return bin(adj[v]).count('1')

def g6_decode(s):
    s = s.strip()
    data = [ord(c) - 63 for c in s]
    n = data[0]; bits = []
    for d in data[1:]:
        for i in range(5, -1, -1): bits.append((d >> i) & 1)
    adj = [0] * n; k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i] |= 1 << j; adj[j] |= 1 << i
            k += 1
    return n, adj

def random_graph(n, p, rng):
    adj = [0] * n
    for i in range(n):
        for j in range(i+1, n):
            if rng.random() < p:
                adj[i] |= 1 << j; adj[j] |= 1 << i
    return adj

def has_square_path(n, adj):
    """Does G contain a spanning square of a Hamiltonian path v1..vn (v_i ~ v_{i+1}, v_i ~ v_{i+2})?"""
    full = (1 << n) - 1
    seq = []
    def dfs(used):
        if used == full: return True
        if len(seq) == 0:
            cand = full
        elif len(seq) == 1:
            cand = adj[seq[-1]] & ~used
        else:
            cand = adj[seq[-1]] & adj[seq[-2]] & ~used
        m = cand & ~used
        while m:
            b = m & -m; w = b.bit_length() - 1; m ^= b
            seq.append(w)
            if dfs(used | b): return True
            seq.pop()
        return False
    return dfs(0)
