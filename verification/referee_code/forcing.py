import sys, os, math, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from collections import deque

def blowup(s):
    """J(s_1..s_k): T_k = path 1..k plus edge {k-2,k}; classes W_i of size s_i. Returns n, adj, cls."""
    k = len(s)
    T = [(i, i+1) for i in range(1, k)] + [(k-2, k)]
    cls = []
    for i, si in enumerate(s, start=1):
        cls += [i] * si
    n = len(cls)
    E = [(a, b) for a in range(n) for b in range(a+1, n)
         if (cls[a], cls[b]) in T or (cls[b], cls[a]) in T]
    return n, from_edges(n, E), cls

def cycle_graph(n):
    return from_edges(n, [(i, (i+1) % n) for i in range(n)])

def grid3(n):
    m = n // 3; E = []
    for i in range(m):
        for r in range(3):
            v = 3*i + r
            if r + 1 < 3: E.append((v, v+1))
            if i + 1 < m: E.append((v, v+3))
    return from_edges(n, E)

def forcing_ii(n, adjJ, want_examples=5):
    """Backward BFS: predecessors of P' under J-adding backbites are backbites of P' (in K_n)
    whose DELETED edge lies in J.  Returns (#reached, total, examples of unreachable)."""
    start = [p for p in ham_paths(n, adjJ)]
    seen = set(start)
    dq = deque(start)
    while dq:
        p = dq.popleft()
        for q in (p, p[::-1]):
            for k in range(2, n):
                if adjJ[q[k-1]] >> q[k] & 1:          # deleted edge q[k-1]q[k] must be in J
                    r = q[k-1::-1] + q[k:]
                    if r[0] > r[-1]: r = r[::-1]
                    if r not in seen:
                        seen.add(r); dq.append(r)
    total = math.factorial(n) // 2
    ex = []
    if len(seen) < total:
        for p in itertools.permutations(range(n)):
            if p[0] < p[-1] and p not in seen:
                ex.append(p)
                if len(ex) >= want_examples: break
    return len(seen), total, ex, len(start)

def forward_closure(n, adjJ, start, limit=10**7):
    """All orderings reachable from `start` by J-adding backbites (in K_n).  Returns (size, J-path found?)."""
    s0 = canon(tuple(start))
    seen = {s0}; dq = deque([s0]); found = None
    while dq:
        p = dq.popleft()
        if found is None and is_ham_path(n, adjJ, p): found = p
        for q in (p, p[::-1]):
            am = adjJ[q[0]]
            for k in range(2, n):
                if am >> q[k] & 1:                    # ADDED edge q[0]q[k] must be in J
                    r = q[k-1::-1] + q[k:]
                    if r[0] > r[-1]: r = r[::-1]
                    if r not in seen:
                        seen.add(r); dq.append(r)
                        if len(seen) > limit: return len(seen), found, False
    return len(seen), found, True

if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'cycle':
        for n in range(3, int(sys.argv[2]) + 1):
            r, t, ex, nj = forcing_ii(n, cycle_graph(n), 30)
            print("C_%d: J-paths=%d reached %d / %d  unreachable=%d  forcing(ii)=%s" % (n, nj, r, t, t - r, r == t), flush=True)
            if ex: print("   examples:", ex[:3], "...", flush=True)
    elif what == 'blowup':
        s = list(map(int, sys.argv[2].split(',')))
        n, adj, cls = blowup(s)
        paths, idx, uf, nc = r_components(n, adj)
        print("J%s: n=%d  #HP(J)=%d  R(J) components=%d" % (tuple(s), n, len(paths), nc), flush=True)
        r, t, ex, nj = forcing_ii(n, adj)
        print("J%s: (ii) reached %d / %d  forcing(ii)=%s  examples=%s" % (tuple(s), r, t, r == t, ex), flush=True)
    elif what == 'grid3':
        n = int(sys.argv[2]); adj = grid3(n)
        paths, idx, uf, nc = r_components(n, adj)
        print("grid3 n=%d: #HP=%d R(J) components=%d" % (n, len(paths), nc), flush=True)
        if n <= 10:
            r, t, ex, nj = forcing_ii(n, adj)
            print("grid3 n=%d: (ii) reached %d / %d forcing(ii)=%s" % (n, r, t, r == t), flush=True)
        if len(sys.argv) > 3:
            start = list(map(int, sys.argv[3].split(',')))
            size, found, complete = forward_closure(n, adj, start)
            print("forward closure from", start, ": size", size, "complete", complete, "J-path found:", found, flush=True)
