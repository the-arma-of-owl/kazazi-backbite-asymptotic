# Literal implementation of the proof of Lemma 2, with assertions on every claim.
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from forcing import blowup

class J:
    def __init__(self, s):
        self.s = s; self.k = len(s)
        self.n, self.adj, self.cls = blowup(s)
        self.size = {i + 1: s[i] for i in range(self.k)}
    def e(self, a, b):
        return bool(self.adj[a] >> b & 1)
    def beta(self, p):
        return sum(1 for i in range(len(p) - 1) if not self.e(p[i], p[i+1]))

def do_bb_front(Jg, p, pos, require_J=True):
    """Backbite at p[0] with target p[pos]; check validity; returns new path, deleted edge."""
    assert pos >= 2, "target is second vertex"
    if require_J: assert Jg.e(p[0], p[pos]), "added edge not in J"
    q, dele = bb(p, p[0], p[pos])
    assert q == bb_front(p, pos)
    return q, dele

def advance(Jg, p, rng, stats):
    """Free endpoint p[0]; fixed endpoint p[-1]."""
    k, cls = Jg.k, Jg.cls
    fixed = p[-1]
    steps = 0
    while cls[p[0]] <= k - 2:
        i = cls[p[0]]
        W = [pos for pos in range(len(p)) if cls[p[pos]] == i + 1]
        assert len(W) == Jg.size[i+1]
        assert all(pos >= 1 for pos in W)                      # every vertex of W_{i+1} has a predecessor
        cands = [pos for pos in W if cls[p[pos-1]] != i]
        assert cands, "no y in W_{i+1} with predecessor outside W_i"
        pos = rng.choice(cands)
        assert pos >= 2                                         # y is not the second vertex
        z, y = p[pos-1], p[pos]
        b0 = Jg.beta(p)
        p, dele = do_bb_front(Jg, p, pos)
        assert dele == frozenset((z, y)) and p[0] == z and p[-1] == fixed
        b1 = Jg.beta(p)
        steps += 1
        if not Jg.e(z, y):
            assert b1 == b0 - 1
            stats['adv_drop'] += 1
            return p, True
        assert b1 == b0
        assert cls[z] > i, "class of new free endpoint does not exceed i"
        assert steps < k
    return p, False

def close(Jg, p, rng, stats):
    k, cls = Jg.k, Jg.cls
    x, x2 = p[0], p[-1]
    Lc = cls[x]; assert cls[x2] == Lc and Lc in (k-1, k)
    Lp = (2*k - 1) - Lc
    targets = [pos for pos in range(len(p)) if cls[p[pos]] in (Lp, k-2)]
    assert len(targets) == Jg.size[Lp] + Jg.size[k-2]
    assert all(Jg.e(x, p[pos]) for pos in targets)
    cands = [pos for pos in targets if cls[p[pos-1]] not in (Lc, k-3)]
    assert len(targets) > Jg.size[Lc] + Jg.size[k-3]
    assert cands
    pos = rng.choice(cands); assert pos >= 2
    z, y = p[pos-1], p[pos]
    b0 = Jg.beta(p)
    p, dele = do_bb_front(Jg, p, pos)
    if not Jg.e(z, y):
        assert Jg.beta(p) == b0 - 1
        stats['close_drop'] += 1
        return p, True
    assert Jg.beta(p) == b0
    assert cls[z] in (k-2, Lp)
    assert p[-1] == x2 and Jg.e(p[0], p[-1])
    return p, False

def descend(Jg, p, stats):
    """Endpoints adjacent in J; rotate until a bad edge is deleted."""
    assert Jg.e(p[0], p[-1])
    b0 = Jg.beta(p)
    assert b0 > 0
    for _ in range(len(p) + 1):
        # rotation = backbite at p[-1] with target p[0]  (adds p[0]p[-1], deletes p[0]p[1])
        assert Jg.e(p[-1], p[0])
        q, dele = bb(p, p[-1], p[0])
        assert dele == frozenset((p[0], p[1]))
        bad = not Jg.e(p[0], p[1])
        p = q
        if bad:
            assert Jg.beta(p) == b0 - 1
            stats['desc_drop'] += 1
            return p
        assert Jg.beta(p) == b0
    raise AssertionError("rotation never deleted a bad edge")

def reach_J(Jg, p, rng, stats):
    """Run the (ii) procedure until beta == 0; return J-path and, if beta was 0 throughout,
    also the closing (a path with J-adjacent endpoints)."""
    p = list(p)
    rounds = 0
    while True:
        b = Jg.beta(p)
        # phase A: free endpoint p[0]
        p, dropped = advance(Jg, p, rng, stats)
        if not dropped:
            p = p[::-1]
            p, dropped = advance(Jg, p, rng, stats)
        if not dropped:
            k = Jg.k
            assert Jg.cls[p[0]] >= k-1 and Jg.cls[p[-1]] >= k-1
            if Jg.cls[p[0]] == Jg.cls[p[-1]]:
                p, dropped = close(Jg, p, rng, stats)
            else:
                assert Jg.e(p[0], p[-1])
        if not dropped:
            assert Jg.e(p[0], p[-1])
            if Jg.beta(p) == 0:
                return p, rounds                      # J-path with adjacent endpoints
            p = descend(Jg, p, stats)
        rounds += 1
        assert Jg.beta(p) == b - 1
        if Jg.beta(p) == 0 and not is_closed(Jg, p):
            # continue: (ii) is done (J-path reached); also bring it to a cyclic path
            pass

def is_closed(Jg, p):
    return Jg.e(p[0], p[-1])

# ---------- property (i): Euler-trail reversals realised by Fact 3, then twin swaps -------------
def fact3(Jg, C, i, j, stats):
    """Reverse the cyclic interval C[i..j] (linear indices, i<=j, t=j-i+1) via Fact 3; returns new list.
    Checks the hypotheses and performs the backbite explicitly."""
    n = len(C); t = j - i + 1
    if t <= 1:
        stats['trivial'] += 1
        return list(C)
    a, b = C[(i-1) % n], C[(j+1) % n]
    u1, ut = C[i], C[j]
    expected = C[:i] + C[i:j+1][::-1] + C[j+1:]
    if a == b:       # interval is everything but one vertex: the reversed cycle is the same cycle
        stats['degenerate_a_eq_b'] += 1
        assert same_cycle(expected, C)
        return expected
    assert Jg.e(a, ut) and Jg.e(u1, b), "Fact 3 hypotheses fail"
    # path = cycle minus edge a u1, read from a: a, C[i-1-1], ..., b, ut, ..., u1
    path = [C[(i-1-r) % n] for r in range(n)]
    assert path[0] == a and path[-1] == u1
    pos = path.index(ut)
    assert path[pos-1] == b and pos >= 2
    q, dele = bb(path, a, ut)
    assert Jg.e(a, ut) and dele == frozenset((b, ut))
    assert {q[0], q[-1]} == {b, u1} and Jg.e(q[0], q[-1])
    assert is_ham_path(Jg.n, Jg.adj, q)
    assert same_cycle(q, expected)
    stats['fact3'] += 1
    return expected

def same_cycle(A, B):
    n = len(A)
    if sorted(A) != sorted(B): return False
    j = B.index(A[0])
    r1 = [B[(j + r) % n] for r in range(n)]
    r2 = [B[(j - r) % n] for r in range(n)]
    return A == r1 or A == r2

def multiplicities(s):
    k = len(s)
    m = {}
    m[(1, 2)] = 2 * s[0]
    for i in range(2, k - 2):
        m[(i, i+1)] = 2 * s[i-1] - m[(i-1, i)]
    A = 2 * s[k-3] - m[(k-3, k-2)]    # a+b, a=m(k-2,k-1), b=m(k-2,k)
    B = 2 * s[k-2]                    # a+c
    Cc = 2 * s[k-1]                   # b+c
    a = (A + B - Cc) // 2; b = A - a; c = B - a
    m[(k-2, k-1)] = a; m[(k-2, k)] = b; m[(k-1, k)] = c
    return m

def cycle_mults(Jg, C):
    from collections import Counter
    n = len(C)
    c = Counter()
    for r in range(n):
        x, y = Jg.cls[C[r]], Jg.cls[C[(r+1) % n]]
        c[(min(x, y), max(x, y))] += 1
    return dict(c)

def random_euler_circuit(m, start, rng):
    """Random Euler circuit (vertex sequence) of multigraph with multiplicities m, via randomised Hierholzer."""
    adjm = {}
    eid = 0
    edges = []
    for (i, j), mult in m.items():
        for _ in range(mult):
            edges.append((i, j)); adjm.setdefault(i, []).append(eid); adjm.setdefault(j, []).append(eid); eid += 1
    for v in adjm: rng.shuffle(adjm[v])
    used = [False] * len(edges)
    stack = [start]; circuit = []
    while stack:
        v = stack[-1]
        while adjm[v] and used[adjm[v][-1]]: adjm[v].pop()
        if adjm[v]:
            e = adjm[v].pop(); used[e] = True
            i, j = edges[e]; w = j if i == v else i
            stack.append(w)
        else:
            circuit.append(stack.pop())
    assert all(used)
    return circuit[::-1]   # closed: first == last

def random_ham_cycle(Jg, rng):
    m = multiplicities(Jg.s)
    seq = random_euler_circuit(m, 1, rng)[:-1]
    pools = {i: [v for v in range(Jg.n) if Jg.cls[v] == i] for i in range(1, Jg.k + 1)}
    for i in pools: rng.shuffle(pools[i])
    C = [pools[c].pop() for c in seq]
    assert all(not pools[i] for i in pools)
    assert all(Jg.e(C[r], C[(r+1) % len(C)]) for r in range(len(C)))
    return C

def vertex_at(T, p):
    return T[p][0] if p < len(T) else T[-1][1]

def rev_trail(T, p, q):
    T[p:q] = [(v, u, lab) for (u, v, lab) in reversed(T[p:q])]

def label_trail(seq):
    """seq: closed vertex sequence of classes (first==last). Returns list of (u,v,label)."""
    from collections import Counter
    cnt = Counter(); T = []
    for r in range(len(seq) - 1):
        u, v = seq[r], seq[r+1]; key = (min(u, v), max(u, v))
        T.append((u, v, cnt[key])); cnt[key] += 1
    return T

def euler_transform(T, Tstar, on_reversal):
    """The Claim: transform labelled trail T into Tstar (same start, end, labelled edges) by
    reversals of closed subtrails.  on_reversal(p, q) is called with vertex positions p<q."""
    T = list(T); m = len(T)
    assert vertex_at(T, 0) == vertex_at(Tstar, 0) and vertex_at(T, m) == vertex_at(Tstar, m)
    key = lambda ed: (min(ed[0], ed[1]), max(ed[0], ed[1]), ed[2])
    assert sorted(map(key, T)) == sorted(map(key, Tstar))
    nrev = 0
    for idx in range(m):
        assert T[:idx] == Tstar[:idx]
        x, y, lab = Tstar[idx]
        for _ in range(3):
            j = next(j for j in range(idx, m) if key(T[j]) == key(Tstar[idx]))
            if j == idx and T[j][0] == x:
                break
            if T[j][0] == y and T[j][1] == x:                       # case 1
                assert vertex_at(T, idx) == x and vertex_at(T, j + 1) == x
                on_reversal(idx, j + 1); rev_trail(T, idx, j + 1); nrev += 1
                assert T[idx] == (x, y, lab)
                break
            # case 3: T[idx..j-1] = A closed at x (non-empty), e = T[j] x->y, B = T[j+1..]
            assert T[j][0] == x and j > idx
            VA = {vertex_at(T, p): p for p in range(idx, j + 1)}
            VB = {}
            for p in range(j + 1, m + 1):
                VB.setdefault(vertex_at(T, p), p)
            common = [z for z in VA if z in VB]
            assert common, "V(A) and V(B) disjoint"
            z = common[0]
            ap = [p for p in range(idx, j + 1) if vertex_at(T, p) == z][0]
            bp = VB[z]
            assert vertex_at(T, ap) == vertex_at(T, bp) == z
            on_reversal(ap, bp); rev_trail(T, ap, bp); nrev += 1
            # now e is traversed y -> x; loop to case 1
        assert T[idx] == Tstar[idx]
    assert T == Tstar
    return nrev

def equivalence_by_proof(Jg, C1, C2, rng, stats):
    n = Jg.n
    # cut both cycles at a W_1 vertex
    c1 = [r for r in range(n) if Jg.cls[C1[r]] == 1][0]
    c2 = [r for r in range(n) if Jg.cls[C2[r]] == 1][0]
    C = C1[c1:] + C1[:c1]; D = C2[c2:] + C2[:c2]
    T = label_trail([Jg.cls[v] for v in C] + [Jg.cls[C[0]]])
    Ts = label_trail([Jg.cls[v] for v in D] + [Jg.cls[D[0]]])
    # labels must be the same multiset: they are (labels 0..m_ij-1 for each pair)
    state = {'C': C}
    def on_rev(p, q):
        Cc = state['C']
        if p == 0 and q == n:
            stats['whole_reversal'] += 1
            state['C'] = [Cc[0]] + Cc[1:][::-1]
            return
        assert Jg.cls[Cc[p]] == Jg.cls[Cc[q % n]] and Cc[p] != Cc[q % n]
        state['C'] = fact3(Jg, Cc, p + 1, q - 1, stats)
    euler_transform(T, Ts, on_rev)
    C = state['C']
    assert [Jg.cls[v] for v in C] == [Jg.cls[v] for v in D]
    # twin swaps
    for i in range(n):
        if C[i] != D[i]:
            j = C.index(D[i]); assert j > i and Jg.cls[C[i]] == Jg.cls[C[j]]
            x, y = C[i], C[j]
            C = fact3(Jg, C, i, j, stats)            # reverse x U y
            assert C[i] == y and C[j] == x
            C = fact3(Jg, C, i + 1, j - 1, stats)    # reverse U^R
            stats['swaps'] += 1
    assert C == D
    return True

if __name__ == '__main__':
    from collections import Counter
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    specs = [(1,2,3,3), (1,2,4,4), (2,3,4,4), (1,2,3,4,4), (3,4,5,6,6), (1,2,3,4,5,5),
             (1,3,5,7,9,9), (2,3,4,5,6,7,7), (5,6,7,8,9,10,11,11), (1,2,3,4,5,6,7,8,9,9),
             (11,12,13,14,15,15)]
    for s in specs:
        Jg = J(s)
        stats = Counter()
        m = multiplicities(s)
        assert all(v > 0 for v in m.values()), m
        for rep in range(reps):
            # (ii) from a random ordering
            p = list(range(Jg.n)); rng.shuffle(p)
            b0 = Jg.beta(p)
            q, rounds = reach_J(Jg, p, rng, stats)
            assert is_ham_path(Jg.n, Jg.adj, q) and Jg.e(q[0], q[-1])
            assert rounds == b0
            # (i): two random Hamiltonian cycles, plus one obtained from the procedure
            C1 = random_ham_cycle(Jg, rng); C2 = random_ham_cycle(Jg, rng)
            assert cycle_mults(Jg, C1) == {kk: v for kk, v in m.items() if v} == cycle_mults(Jg, C2)
            assert cycle_mults(Jg, q) == cycle_mults(Jg, C1)
            equivalence_by_proof(Jg, C1, C2, rng, stats)
            equivalence_by_proof(Jg, q, C1, rng, stats)
            # (ii) applied to a J-path: stays in J and ends cyclic
            hp = C1[:]; cut = rng.randrange(Jg.n); hp = hp[cut:] + hp[:cut]
            # make a non-cyclic J-path by one J-backbite if possible
            q2, r2 = reach_J(Jg, hp, rng, stats)
            assert r2 == 0
        print("J%s n=%d: %d reps OK; m=%s; stats=%s" % (s, Jg.n, reps, m, dict(stats)), flush=True)
