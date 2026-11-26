# Bağımsız kaba kuvvet: yayılan merdiven / d13 / P^2 içeriyor mu? (n=8, tüm permütasyonlar)
import sys, itertools, random, subprocess
def g6(n, E):
    S = set(E); bits = [1 if (i,j) in S else 0 for j in range(1,n) for i in range(j)]
    while len(bits) % 6: bits.append(0)
    out = chr(n+63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k+6]: v = 2*v + b
        out += chr(v+63)
    return out
def pattern(name, n):
    if name == 'ladder':
        m = n//2; E = []
        for i in range(m):
            E.append((2*i, 2*i+1))
            if i+1 < m: E += [(2*i, 2*i+2), (2*i+1, 2*i+3)]
        return E
    if name == 'd13': return [(i, i+d) for i in range(n) for d in (1,3) if i+d < n]
    if name == 'sq':  return [(i, i+d) for i in range(n) for d in (1,2) if i+d < n]
def contains(n, adj, P):
    for perm in itertools.permutations(range(n)):
        if all(adj[perm[a]][perm[b]] for a, b in P): return 1
    return 0
random.seed(12345); n = 8
lines = []; truth = []
for trial in range(400):
    p = random.choice([0.45, 0.55, 0.65, 0.75])
    E = [(i, j) for i in range(n) for j in range(i+1, n) if random.random() < p]
    adj = [[0]*n for _ in range(n)]
    for a, b in E: adj[a][b] = adj[b][a] = 1
    lines.append(g6(n, E))
    truth.append((contains(n, adj, pattern('ladder', n)), contains(n, adj, pattern('d13', n)), contains(n, adj, pattern('sq', n))))
out = subprocess.run([sys.argv[1], '-T'], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.split('\n')
bad = 0; cnt = [0, 0, 0]
for t, o in zip(truth, out):
    c = tuple(map(int, o.split()[1:4]))
    if c != t: bad += 1; print('UYUSMAZLIK', o, t)
    cnt = [cnt[i] + t[i] for i in range(3)]
print('test edilen', len(truth), 'uyuşmazlık', bad, 'pozitif (ladder,d13,sq):', cnt)
