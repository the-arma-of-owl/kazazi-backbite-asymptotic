# Küçük yardımcı: kenar listesinden graph6 kodu üret.
def to_g6(n, edges):
    E = set((min(a,b), max(a,b)) for a,b in edges)
    bits = [1 if (i,j) in E else 0 for j in range(1,n) for i in range(j)]
    while len(bits) % 6: bits.append(0)
    out = chr(n+63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k+6]: v = 2*v + b
        out += chr(v+63)
    return out

def H(t):
    # a=0,b=1,h=2..t+1, x=t+2 (a'ya bağlı), y=t+3 (b'ye bağlı)
    V = list(range(t+2)); E = [(i,j) for i in V for j in V if i<j and not (i==0 and j==1)]
    E += [(t+2,0),(t+3,1)]
    return t+4, E

def A(m, n0, E0):
    # S = n0..n0+m-1, Z = n0+m..n0+2m-1 ; S tam iki parçalı (V(H) ∪ Z)
    S = range(n0, n0+m); Z = range(n0+m, n0+2*m)
    E = list(E0) + [(s,v) for s in S for v in list(range(n0))+list(Z)]
    return n0+2*m, E

if __name__ == '__main__':
    import sys
    tests = []
    n,E = H(2); tests.append(to_g6(n,E))
    n,E = H(3); tests.append(to_g6(n,E))
    n0,E0 = H(2); n,E = A(1,n0,E0); tests.append(to_g6(n,E))
    n0,E0 = H(2); n,E = A(2,n0,E0); tests.append(to_g6(n,E))
    for m in (6,7,8): tests.append(to_g6(m, [(i,j) for i in range(m) for j in range(i+1,m)]))
    print("\n".join(tests))
