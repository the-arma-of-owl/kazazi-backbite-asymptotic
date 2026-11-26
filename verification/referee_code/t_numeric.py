import sys, os, math, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *

# ---------- Fact 2: count of crossing indices -------------
rng = random.Random(5)
tested = 0
for _ in range(3000):
    h = rng.randint(4, 14)
    adj = random_graph(h, rng.uniform(0.2, 0.95), rng)
    P = list(range(h)); rng.shuffle(P)
    # force P to be a path of F
    for i in range(h - 1):
        adj[P[i]] |= 1 << P[i+1]; adj[P[i+1]] |= 1 << P[i]
    a, b = P[0], P[-1]
    if adj[a] >> b & 1: continue
    S = {i for i in range(1, h) if adj[a] >> P[i] & 1}          # 1-indexed i with a w_{i+1}: P[i] = w_{i+1}
    T = {i for i in range(1, h) if adj[b] >> P[i-1] & 1}        # b w_i: P[i-1] = w_i
    cross = S & T
    assert len(S) == deg(adj, a) and len(T) == deg(adj, b)
    assert len(cross) >= deg(adj, a) + deg(adj, b) - (h - 1)
    for i in cross:
        assert 2 <= i <= h - 2
        q1, d1 = bb(tuple(P), a, P[i])          # bb(a, w_{i+1})
        assert d1 == frozenset((P[i-1], P[i])) and {q1[0], q1[-1]} == {P[i-1], b} and adj[P[i-1]] >> b & 1
        q2, d2 = bb(tuple(P), b, P[i-1])        # bb(b, w_i)
        assert d2 == d1 and {q2[0], q2[-1]} == {a, P[i]} and adj[a] >> P[i] & 1
    tested += 1
print("Fact 2: tested", tested, "paths: bound and both backbites OK")

# ---------- Lemma 5 / Section 5 inequalities on a fine grid of alpha (exact rationals) ----------
bad = []
for N in range(32, 5000, 7):
    al = Fr(1, N)                        # alpha <= 1/32
    for k in [math.ceil(1 / al), math.ceil(1 / al) + 1, 3 * math.ceil(1 / al)]:
        if not ((Fr(1, 2) + 16 * al) * (k - 1) >= (Fr(1, 2) + 12 * al) * k + 3 * al * k): bad.append(('Edq', al, k))
        if not (Fr(18) * al**2 * k**2 / (k - 1) >= 18 * al**2 * k): bad.append(('hoef1', al, k))
        if not (12 * al * k >= 1): bad.append(('12ak', al, k))
        for t in [math.ceil(k / al), math.ceil(k / al) + 5]:
            if not (Fr(t + 1, t + k) >= 1 - al): bad.append(('t', al, k, t))
            s_hi = k * (t + k); s_lo = k * (t + 1)
            # S-vertices: (1/2+12a) k (t+1) >= (1/2+8a) s for all s <= k(t+k)
            if not ((Fr(1, 2) + 12 * al) * s_lo >= (Fr(1, 2) + 8 * al) * s_hi): bad.append(('dS', al, k, t))
            if not ((Fr(1, 2) + 10 * al) * s_lo >= (Fr(1, 2) + 8 * al) * s_hi): bad.append(('typ', al, k, t))
    if not (2 * al / (Fr(1, 2) + 12 * al) >= 2 * al): bad.append(('pi', al))
    # Section 5
    sstar = math.ceil(Fr(3) / (4 * al))
    for s in [sstar, sstar + 1, 10 * sstar]:
        for j in [1, 2, 5, 100, 10**6]:
            if not (8 * al * s + 14 * al * j - 3 >= 4 * al * (s + j)): bad.append(('tail', al, s, j))
            if not ((Fr(1, 2) + 8 * al) * s >= Fr(s + 1, 2) + 2): bad.append(('j1empty', al, s))
            # mean bound: (1/2+8a)s + (1/2+14a)j - 1 - ((s+j)/2+2) = 8as + 14aj - 3
            if not ((Fr(1, 2) + 8 * al) * s + (Fr(1, 2) + 14 * al) * j - 1 - (Fr(s + j, 2) + 2) == 8 * al * s + 14 * al * j - 3): bad.append(('alg', al))
    if not ((Fr(1, 2) + 8 * al) * sstar >= Fr(sstar, 2) + 2): bad.append(('j0', al))
    # (1/2+14a)(j-1) >= (1/2+14a) j - 1
    if not (Fr(1, 2) + 14 * al <= 1): bad.append(('mean-1', al))
print("Section 4/5 inequalities: failures =", bad[:10], "count", len(bad))

# ---------- Hoeffding (hypergeometric lower tail) sanity ----------
def hyp_pmf(Npop, K, q, x):
    return math.comb(K, x) * math.comb(Npop - K, q - x) / math.comb(Npop, q)
worst = 0
for _ in range(2000):
    Npop = rng.randint(2, 120); K = rng.randint(0, Npop); q = rng.randint(1, Npop)
    mu = q * K / Npop
    for u in [0.5, 1, 2, 3, 5, 0.1 * q, 0.3 * q]:
        thr = mu - u
        tail = sum(hyp_pmf(Npop, K, q, x) for x in range(max(0, q - (Npop - K)), min(q, K) + 1) if x <= thr + 1e-12)
        bound = math.exp(-2 * u * u / q)
        worst = max(worst, tail - bound)
print("Hoeffding w/o replacement: max(tail - bound) over 14000 cases =", worst)

# ---------- size of the constants (Remark 1) ----------
def constants(gamma):
    al = gamma / 16
    k = math.ceil(1 / al)
    while not (k * math.exp(-18 * al * al * k) < 0.25 and math.exp(-32 * al * al * k) / al**2 < 0.25):
        k = math.ceil(k * 1.01)
    s = math.ceil(3 / (4 * al))
    c = 32 * al * al
    def tail_sum(s):
        tot = 0.0; j = 1
        while True:
            term = (s + j + 1) * math.exp(-c * (s + j)); tot += term
            if term < 1e-18 and j > 10: break
            j += 1
        return tot
    while tail_sum(s) >= 1: s = math.ceil(s * 1.02)
    t = max(math.ceil(k / al), s)
    L = t + k
    # Erdos: c n^k > (kn)^(k - L^{1-k})  ->  log2 n_0 ~ L^{k-1} * (C(k,2) + 2 + k log2 k)
    log10_log2_n0 = (k - 1) * math.log10(L) + math.log10(math.comb(k, 2) + 2 + k * math.log2(k))
    return al, k, s, t, L, log10_log2_n0
for g in [0.5, 0.25, 0.1, 0.05]:
    al, k, s, t, L, ll = constants(g)
    print("gamma=%.3f alpha=%.5f k~%d s*~%d t~%d L~%d  log10(log2 n0) ~ %.4g  (doubly exponential)" % (g, al, k, s, t, L, ll))
