# Aday iskeletler J: kenar listesi üretir.  Kullanım: python3 -I aday.py <ad> <n> [g6]
import sys
def edges(name, n):
    E = set()
    def add(a, b):
        if 0 <= a < n and 0 <= b < n and a != b: E.add((min(a,b), max(a,b)))
    if name == 'sq':
        for i in range(n): add(i, i+1); add(i, i+2)
    elif name.startswith('d'):            # ör. d13, d135 : yol mesafeleri
        ds = [int(c) for c in name[1:]]
        for i in range(n):
            for d in ds: add(i, i+d)
    elif name.startswith('c'):            # ör. c13 : döngüsel mesafeler
        ds = [int(c) for c in name[1:]]
        for i in range(n):
            for d in ds: add(i, (i+d) % n)
    elif name == 'ladder':                # P_m □ K_2, n=2m
        m = n//2
        for i in range(m):
            add(2*i, 2*i+1)
            if i+1 < m: add(2*i, 2*i+2); add(2*i+1, 2*i+3)
    elif name == 'prism':                 # C_m □ K_2
        m = n//2
        for i in range(m):
            add(2*i, 2*i+1); j = (i+1) % m; add(2*i, 2*j); add(2*i+1, 2*j+1)
    elif name == 'mobius':
        m = n//2
        for i in range(m):
            add(2*i, 2*i+1)
            if i+1 < m: add(2*i, 2*i+2); add(2*i+1, 2*i+3)
        add(0, 2*(m-1)+1); add(1, 2*(m-1))
    elif name.startswith('blob'):          # P_k[\bar K_s] : ardışık bloklar arası tam
        s = int(name[4:]); k = n // s
        for i in range(k-1):
            for a in range(s):
                for b in range(s): add(i*s+a, (i+1)*s+b)
    elif name == 'grid3':                 # P_m □ P_3
        m = n//3
        for i in range(m):
            for r in range(3):
                v = 3*i + r
                if r+1 < 3: add(v, v+1)
                if i+1 < m: add(v, v+3)
    else:
        raise SystemExit('bilinmeyen ad')
    return sorted(E)

def to_g6(n, E):
    S = set(E)
    bits = [1 if (i,j) in S else 0 for j in range(1,n) for i in range(j)]
    while len(bits) % 6: bits.append(0)
    out = chr(n+63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k+6]: v = 2*v + b
        out += chr(v+63)
    return out

if __name__ == '__main__':
    name, n = sys.argv[1], int(sys.argv[2])
    E = edges(name, n)
    if len(sys.argv) > 3: print(to_g6(n, E))
    else:
        print(n, len(E))
        for a, b in E: print(a, b)
