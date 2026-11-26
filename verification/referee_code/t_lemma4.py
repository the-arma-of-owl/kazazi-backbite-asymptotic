# Tests of Lemma 4 (vertex extension): explicit move bookkeeping + brute-force component claims.
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *

def e(adj, a, b): return bool(adj[a] >> b & 1)

def attachment(D, a, direction, v):
    """Attachment to Ham cycle D (list) at a: v, a, ..., b where b is the D-neighbour of a
    in direction -direction; the part a..b traverses D from a omitting edge ab."""
    h = len(D); i = D.index(a)
    return (v,) + tuple(D[(i + direction * r) % h] for r in range(h))

def is_attachment(adj, D, p, v):
    """Is p (in either orientation) an attachment to D?"""
    h = len(D)
    for q in (p, p[::-1]):
        if q[0] != v or not e(adj, v, q[1]): continue
        a = q[1]
        if q == attachment(D, a, +1, v) or q == attachment(D, a, -1, v): return True
    return False

def insert_v(P, edge, v):
    x, y = tuple(edge)
    for i in range(len(P) - 1):
        if {P[i], P[i+1]} == {x, y}:
            return P[:i+1] + (v,) + P[i+1:]
    raise ValueError

def eligible(adj, P, v):
    return [frozenset((P[i], P[i+1])) for i in range(len(P) - 1) if e(adj, v, P[i]) and e(adj, v, P[i+1])]

def crossings(adj, P):
    h = len(P); a, b = P[0], P[-1]
    return [i for i in range(h - 1) if e(adj, a, P[i+1]) and e(adj, b, P[i])]   # 0-indexed i: w_{i+1}, w_{i+2}

# ---------------- Part A: explicit bookkeeping ----------------
def partA(rng, trials):
    cnt = 0
    for _ in range(trials):
        h = rng.randint(4, 12)
        D = list(range(h)); rng.shuffle(D)
        E = [(D[i], D[(i+1) % h]) for i in range(h)]
        p_extra = rng.random()
        E += [(a, b) for a in range(h) for b in range(a+1, h) if rng.random() < p_extra]
        v = h
        Nv = [x for x in range(h) if rng.random() < 0.6]
        if len(Nv) < 2: Nv = rng.sample(range(h), 2)
        E += [(v, x) for x in Nv]
        n = h + 1
        adj = from_edges(n, E)
        for a in Nv:
            for direction in (+1, -1):
                att = attachment(D, a, direction, v)
                assert is_ham_path(n, adj, att)
                b = att[-1]
                # same attachment point, other direction: backbite from b with target a
                q, dele = bb(att, b, a)
                assert e(adj, b, a)
                assert q[::-1] == attachment(D, a, -direction, v) or q == attachment(D, a, -direction, v)
                assert q[0] == v or q[-1] == v
                qq = q if q[0] == v else q[::-1]
                assert qq == attachment(D, a, -direction, v), (att, qq)
                for c in Nv:
                    if c == a: continue
                    ci = att.index(c)
                    A = att[2:ci]; B = att[ci+1:-1] if c != b else ()
                    if c != b:
                        assert att == (v, a) + A + (c,) + B + (b,)
                        q1, _ = bb(att, v, c)
                        assert q1 == A[::-1] + (a, v, c) + B + (b,), "first move"
                        q2, _ = bb(q1, b, a)
                        q2o = q2 if q2[0] == v else q2[::-1]
                        assert q2o == (v, c) + B + (b, a) + A, "second move"
                    else:
                        A = att[2:-1]
                        q1, _ = bb(att, v, b)
                        assert q1 == A[::-1] + (a, v, b)
                        q2, _ = bb(q1, b, a)
                        q2o = q2 if q2[0] == v else q2[::-1]
                        assert q2o == (v, b, a) + A
                    assert is_attachment(adj, D, q2o, v)
                    cnt += 1
        # D_xy: deleting vy gives attachment at x
        for i in range(h):
            x, y = D[i], D[(i+1) % h]
            if e(adj, v, x) and e(adj, v, y):
                Dxy = D[:i+1] + [v] + D[i+1:]
                # path = Dxy minus edge v-y, read from v
                j = Dxy.index(v)
                path = tuple(Dxy[(j - r) % n] for r in range(n))   # v, x, ..., y
                assert path[1] == x and path[-1] == y
                assert is_attachment(adj, D, path, v)
                cnt += 1
    return cnt

def partA_lifts(rng, trials):
    cnt = 0
    for _ in range(trials):
        h = rng.randint(6, 12)
        n = h + 1; v = h
        adj = random_graph(h, rng.uniform(0.5, 0.95), rng) + [0]
        for x in range(h):
            if rng.random() < 0.75: adj[x] |= 1 << v; adj[v] |= 1 << x
        # random Ham path of H via random DFS
        P = random_ham_path(h, adj, rng)
        if P is None: continue
        el = eligible(adj, P, v)
        # (a) second case: crossing avoiding e, f
        if not e(adj, P[0], P[-1]) and len(el) >= 2:
            ef = rng.sample(el, 2)
            for i in crossings(adj, P):
                if frozenset((P[i], P[i+1])) in ef: continue
                # bb(a, w_{i+2}) in 0-index: target P[i+1]
                Pp, dele = bb(P, P[0], P[i+1])
                assert e(adj, Pp[0], Pp[-1])                       # adjacent endpoints
                for f in ef:
                    Pe = insert_v(P, f, v)
                    q, d2 = bb(Pe, P[0], P[i+1])
                    assert d2 == dele
                    assert canon(q) == canon(insert_v(Pp, f, v))
                # the symmetric one: bb(b, w_i)
                Pp2, dele2 = bb(P, P[-1], P[i])
                assert dele2 == dele and e(adj, Pp2[0], Pp2[-1])
                assert P[0] in (Pp2[0], Pp2[-1])
                for f in ef:
                    Pe = insert_v(P, f, v)
                    q, d2 = bb(Pe, P[-1], P[i])
                    assert canon(q) == canon(insert_v(Pp2, f, v))
                cnt += 1
        # (b): any backbite P -> Q in H, eligible e != deleted edge
        for end in (P[0], P[-1]):
            q0 = P if P[0] == end else P[::-1]
            for k in range(2, h):
                if not e(adj, end, q0[k]): continue
                Q, dele = bb(P, end, q0[k])
                for f in el:
                    if f == dele: continue
                    Pe = insert_v(P, f, v)
                    q, d2 = bb(Pe, end, q0[k])
                    assert d2 == dele
                    assert canon(q) == canon(insert_v(Q, f, v))
                    cnt += 1
    return cnt

def random_ham_path(h, adj, rng, tries=50):
    full = (1 << h) - 1
    for _ in range(tries):
        s = rng.randrange(h); path = [s]; used = 1 << s
        def dfs(used):
            if used == full: return True
            nb = [w for w in range(h) if adj[path[-1]] >> w & 1 and not used >> w & 1]
            rng.shuffle(nb)
            for w in nb[:3]:
                path.append(w)
                if dfs(used | 1 << w): return True
                path.pop()
            return False
        if dfs(used): return tuple(path)
    return None

# ---------------- Part B: brute-force component claims ----------------
def ham_cycles_of(h, adjH, pathsH):
    seen = set(); out = []
    for p in pathsH:
        if e(adjH, p[0], p[-1]):
            # canonical cycle: rotate to start at 0, direction with smaller second element
            c = list(p); i = c.index(0); c = c[i:] + c[:i]
            if c[1] > c[-1]: c = [c[0]] + c[1:][::-1]
            t = tuple(c)
            if t not in seen: seen.add(t); out.append(list(t))
    return out

def partB(rng, trials, hmin, hmax, mode):
    stats = dict(graphs=0, B1=0, B2=0, B3=0, B4=0, B5=0, full_tested=0, full_ok=0, rem3_tested=0, rem3_ok=0)
    for _ in range(trials):
        h = rng.randint(hmin, hmax); v = h; n = h + 1
        if mode == 'weak':
            adjH = random_graph(h, rng.uniform(0.35, 0.9), rng)
            Nv = [x for x in range(h) if rng.random() < rng.uniform(0.3, 0.9)]
        elif mode == 'sparse':
            adjH = random_graph(h, rng.uniform(0.25, 0.55), rng)
            Nv = rng.sample(range(h), rng.randint(2, max(2, h // 2 + 1)))
        elif mode == 'lemma4':
            # delta(H) >= h/2+2 : complement has max degree <= h-1-(h/2+2)
            while True:
                adjH = random_graph(h, rng.uniform(0.7, 1.0), rng)
                if min(deg(adjH, x) for x in range(h)) >= h / 2 + 2: break
            d = rng.randint(int(-(-(h / 2 + 2) // 1)), h)
            Nv = rng.sample(range(h), d)
        elif mode == 'remark3':
            while True:
                adjH = random_graph(h, rng.uniform(0.4, 1.0), rng)
                ok = all(deg(adjH, x) + deg(adjH, y) >= h + 2 for x in range(h) for y in range(x+1, h) if not e(adjH, x, y))
                if ok: break
            dmin = -(-(h + 3) // 2)
            d = rng.randint(dmin, h)
            Nv = rng.sample(range(h), d)
        adj = adjH[:] + [0]
        for x in Nv: adj[x] |= 1 << v; adj[v] |= 1 << x
        pathsH = ham_paths(h, adjH)
        if not pathsH: continue
        paths, idx, uf, nc = r_components(n, adj)
        if not paths: continue
        stats['graphs'] += 1
        if nc > 1: stats['R(G)_disconnected'] = stats.get('R(G)_disconnected', 0) + 1
        if stats['graphs'] % 25 == 0: print('progress', mode, dict(stats), flush=True)
        comp = lambda p: uf.find(idx[canon(p)])
        cycles = ham_cycles_of(h, adjH, pathsH)
        attcomp = {}
        for D in cycles:
            atts = [attachment(D, a, dr, v) for a in Nv for dr in (+1, -1)]
            cs = {comp(p) for p in atts}
            if atts:
                assert len(cs) == 1, ("B1 fails", D, Nv); stats['B1'] += 1
                attcomp[tuple(D)] = cs.pop()
            for i in range(h):
                x, y = D[i], D[(i+1) % h]
                if x in Nv and y in Nv:
                    Dxy = D[:i+1] + [v] + D[i+1:]
                    for r in range(n):
                        p = tuple(Dxy[r+1:] + Dxy[:r+1])   # delete edge Dxy[r]Dxy[r+1]
                        assert comp(p) == attcomp[tuple(D)], "B2 fails"
                    stats['B2'] += 1
        # lifts
        Hidx = {p: i for i, p in enumerate(pathsH)}
        for P in pathsH:
            el = eligible(adj, P, v)
            lifts = [insert_v(P, f, v) for f in el]
            if e(adjH, P[0], P[-1]) and lifts:
                assert len({comp(q) for q in lifts}) == 1, "B3 fails"; stats['B3'] += 1
            elif len(el) >= 2:
                cr = [frozenset((P[i], P[i+1])) for i in crossings(adjH, P)]
                for f1, f2 in itertools.combinations(el, 2):
                    if any(c not in (f1, f2) for c in cr):
                        assert comp(insert_v(P, f1, v)) == comp(insert_v(P, f2, v)), "B4 fails"
                        stats['B4'] += 1
            # (b)
            for end in (P[0], P[-1]):
                q0 = P if P[0] == end else P[::-1]
                for k in range(2, h):
                    if not e(adjH, end, q0[k]): continue
                    Q, dele = bb(P, end, q0[k])
                    for f in el:
                        if f != dele:
                            assert comp(insert_v(P, f, v)) == comp(insert_v(Q, f, v)), "B5 fails"
                            stats['B5'] += 1
        if mode in ('lemma4', 'remark3'):
            _, _, _, ncH = r_components(h, adjH, pathsH)
            if ncH == 1:
                key = 'full' if mode == 'lemma4' else 'rem3'
                stats[key + '_tested'] += 1
                if nc == 1: stats[key + '_ok'] += 1
                else: print("COUNTEREXAMPLE?", mode, h, adjH, Nv, nc, flush=True)
    return stats

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
    part = sys.argv[1]
    if part == 'A':
        print("Part A attachments/moves checked:", partA(rng, 400), flush=True)
        print("Part A lifts/crossings checked:", partA_lifts(rng, 400), flush=True)
    elif part == 'Bweak':
        print("Part B weak:", partB(rng, int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), 'weak'), flush=True)
    elif part == 'Bsparse':
        print("Part B sparse:", partB(rng, int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), 'sparse'), flush=True)
    elif part == 'Blemma4':
        print("Part B lemma4 hyp:", partB(rng, int(sys.argv[3]), 6, 8, 'lemma4'), flush=True)
    elif part == 'Bremark3':
        print("Part B remark3 hyp:", partB(rng, int(sys.argv[3]), 6, 8, 'remark3'), flush=True)
