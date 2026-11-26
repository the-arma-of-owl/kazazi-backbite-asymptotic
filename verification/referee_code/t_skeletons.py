import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from forcing import forcing_ii, grid3
def skel(name, n):
    E = []
    if name == 'sq':
        E = [(i, i+d) for i in range(n) for d in (1, 2) if i + d < n]
    elif name == 'ladder':
        m = n // 2
        for i in range(m):
            E.append((2*i, 2*i+1))
            if i + 1 < m: E += [(2*i, 2*i+2), (2*i+1, 2*i+3)]
    elif name == 'prism':
        m = n // 2
        for i in range(m):
            j = (i + 1) % m; E += [(2*i, 2*i+1), (2*i, 2*j), (2*i+1, 2*j+1)]
    elif name == 'd13':
        E = [(i, i+d) for i in range(n) for d in (1, 3) if i + d < n]
    elif name == 'c13':
        E = [(i, (i+d) % n) for i in range(n) for d in (1, 3)]
    elif name == 'grid3':
        return grid3(n)
    return from_edges(n, E)
for name, n in [(a, int(b)) for a, b in (x.split(':') for x in sys.argv[1:])]:
    adj = skel(name, n)
    paths, idx, uf, nc = r_components(n, adj)
    r, t, ex, nj = forcing_ii(n, adj)
    print("%s n=%d: #HP=%d R(J) comps=%d  (ii) reached %d/%d forcing=%s" % (name, n, len(paths), nc, r, t, nc == 1 and r == t), flush=True)
