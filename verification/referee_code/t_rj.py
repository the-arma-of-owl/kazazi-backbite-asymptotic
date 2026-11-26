import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from forcing import blowup, forward_closure, grid3
for spec in sys.argv[1:]:
    s = list(map(int, spec.split(',')))
    n, adj, cls = blowup(s)
    paths, idx, uf, nc = r_components(n, adj)
    print("J%s: n=%d #HP(J)=%d R(J) components=%d" % (tuple(s), n, len(paths), nc), flush=True)
