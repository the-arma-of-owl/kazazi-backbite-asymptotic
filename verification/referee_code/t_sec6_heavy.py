import sys, os, subprocess, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from multiprocessing import Pool

def geng(args):
    out = subprocess.run(['geng', '-q'] + args, capture_output=True, text=True).stdout.split()
    return out

def ore(n, adj):
    return all(deg(adj, x) + deg(adj, y) >= n for x in range(n) for y in range(x+1, n) if not adj[x] >> y & 1)

# ---------- R(G) connectivity ----------
def job_conj(g6, use_square=True):
    n, adj = g6_decode(g6)
    if use_square and has_square_path(n, adj):
        return (g6, 'square', None, None)
    paths, idx, uf, nc = r_components(n, adj)
    return (g6, 'direct', len(paths), nc)

def job_conj_direct(g6):
    return job_conj(g6, use_square=False)

# ---------- fixed endpoint R_b ----------
def rb_all_connected(n, adj):
    full = (1 << n) - 1
    bad_b = []
    for b in range(n):
        paths = []
        path = [b]
        def dfs(used, last):
            if used == full:
                paths.append(tuple(path)); return
            m = adj[last] & ~used
            while m:
                bt = m & -m; w = bt.bit_length() - 1; m ^= bt
                path.append(w); dfs(used | bt, w); path.pop()
        dfs(1 << b, b)
        if not paths: continue
        idx = {p: i for i, p in enumerate(paths)}
        uf = UF(len(paths))
        for i, p in enumerate(paths):
            w = p[-1]; am = adj[w]
            for k in range(0, n - 2):
                if am >> p[k] & 1:
                    q = p[:k+1] + p[k+1:][::-1]
                    uf.union(i, idx[q])
        nc = len({uf.find(i) for i in range(len(paths))})
        if nc > 1: bad_b.append((b, nc))
    return bad_b

def job_rb(g6):
    n, adj = g6_decode(g6)
    bad = rb_all_connected(n, adj)
    return (g6, min(deg(adj, v) for v in range(n)), bad)

# ---------- closure ----------
def job_closure(args):
    g6, thr = args
    n, adj = g6_decode(g6)
    res = []
    pairs = [(u, v) for u in range(n) for v in range(u+1, n)
             if not adj[u] >> v & 1 and deg(adj, u) + deg(adj, v) >= thr]
    if not pairs: return (g6, 0, [])
    _, _, _, ncG = r_components(n, adj)
    for u, v in pairs:
        a2 = adj[:]; a2[u] |= 1 << v; a2[v] |= 1 << u
        _, _, _, nc2 = r_components(n, a2)
        if nc2 <= 1 and ncG >= 2: res.append(('BACK', u, v, ncG, nc2))
        if ncG <= 1 and nc2 >= 2: res.append(('FWD', u, v, ncG, nc2))
    return (g6, len(pairs), res)

def has_sq_g6(g6):
    n, adj = g6_decode(g6)
    return has_square_path(n, adj)

if __name__ == '__main__':
    mode = sys.argv[1]
    procs = int(os.environ.get('NPROC', '20'))
    if mode == 'conj':          # conj n d [direct] [sample]
        n, d = sys.argv[2], sys.argv[3]
        gs = geng(['-d' + d, n])
        direct = len(sys.argv) > 4 and sys.argv[4] == 'direct'
        with Pool(procs) as pool:
            res = pool.map(job_conj_direct if direct else job_conj, gs, chunksize=64)
        sq = sum(1 for r in res if r[1] == 'square')
        dr = [r for r in res if r[1] == 'direct']
        nohp = sum(1 for r in dr if r[2] == 0)
        disc = [r for r in dr if r[2] > 0 and r[3] != 1]
        print("n=%s d>=%s: total=%d contain_square=%d checked_directly=%d (no_HP=%d) disconnected=%d max_paths=%d"
              % (n, d, len(res), sq, len(dr), nohp, len(disc), max([r[2] for r in dr] or [0])), flush=True)
        for r in disc[:20]: print("  DISCONNECTED", r)
    elif mode == 'conj_sample':   # conj_sample n d samplesize seed : sample among non-square graphs
        n, d, ss, seed = sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
        gs = geng(['-d' + d, n])
        rng = random.Random(seed); rng.shuffle(gs)
        with Pool(procs) as pool:
            sq_flags = pool.map(has_sq_g6, gs[:ss * 6], chunksize=64)
        cand = [g for g, f in zip(gs[:ss * 6], sq_flags) if not f][:ss]
        with Pool(procs) as pool:
            res = pool.map(job_conj_direct, cand, chunksize=4)
        disc = [r for r in res if r[2] > 0 and r[3] != 1]
        print("sample n=%s d>=%s: non-square graphs sampled=%d, no_HP=%d, disconnected=%d"
              % (n, d, len(res), sum(1 for r in res if r[2] == 0), len(disc)), flush=True)
    elif mode == 'ore':
        n = sys.argv[2]
        gs = geng(['-c', n])
        gs = [g for g in gs if ore(*g6_decode(g))]
        with Pool(procs) as pool:
            res = pool.map(job_conj_direct, gs, chunksize=8)
        disc = [r for r in res if r[3] != 1]
        print("Ore n=%s: graphs=%d disconnected=%d" % (n, len(res), len(disc)), flush=True)
    elif mode == 'rb':           # rb n d
        n, d = sys.argv[2], sys.argv[3]
        extra = sys.argv[4:]
        gs = geng(['-d' + d] + extra + [n])
        with Pool(procs) as pool:
            res = pool.map(job_rb, gs, chunksize=8)
        fails = [r for r in res if r[2]]
        from collections import Counter
        print("R_b n=%s d>=%s %s: graphs=%d failing=%d; failing by delta=%s"
              % (n, d, extra, len(res), len(fails), dict(Counter(r[1] for r in fails))), flush=True)
    elif mode == 'closure':      # closure n thr_offset
        n = int(sys.argv[2]); off = int(sys.argv[3])
        gs = geng(['-c', str(n)])
        with Pool(procs) as pool:
            res = pool.map(job_closure, [(g, n + off) for g in gs], chunksize=16)
        pairs = sum(r[1] for r in res)
        back = [(r[0],) + x for r in res for x in r[2] if x[0] == 'BACK']
        fwd = [(r[0],) + x for r in res for x in r[2] if x[0] == 'FWD']
        print("closure n=%d thr=n%+d: graphs=%d pairs=%d backward_violations=%d forward_violations=%d"
              % (n, off, len(res), pairs, len(back), len(fwd)), flush=True)
        for b in back[:20]: print("  BACK", b)

