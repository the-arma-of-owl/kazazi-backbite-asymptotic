// frontonly.c — Arka uç b SABİT; yalnız ön uçtan J-kenarı ekleyen backbite'larla
// her permütasyondan (son eleman b) J'nin b'de biten bir Hamilton yoluna ulaşılır mı?
// Girdi: stdin "n m b" + m kenar. n <= 12.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n, B; static unsigned J[16]; static uint64_t fact[16];
static int others[16]; // b dışındaki tepeler
static uint64_t rank_front(const int *p) { // p[0..n-2] (b hariç) -> (n-1)! içinde sıra
    uint64_t r = 0; unsigned used = 0;
    for (int i = 0; i < n - 1; i++) {
        int idx = 0; for (int k = 0; k < n - 1; k++) if (others[k] == p[i]) { idx = k; break; }
        int smaller = __builtin_popcount(((1u << idx) - 1) & ~used);
        r += (uint64_t)smaller * fact[n - 2 - i]; used |= 1u << idx;
    }
    return r;
}
static void unrank_front(uint64_t r, int *p) {
    unsigned used = 0;
    for (int i = 0; i < n - 1; i++) {
        uint64_t f = fact[n - 2 - i]; int k = (int)(r / f); r %= f;
        for (int v = 0; v < n - 1; v++) if (!((used >> v) & 1)) { if (k == 0) { p[i] = others[v]; used |= 1u << v; break; } k--; }
    }
    p[n - 1] = B;
}
static uint8_t *mark; static uint32_t *q; static uint64_t qh, qt, qc;
static inline int getb(uint64_t r){return (mark[r>>3]>>(r&7))&1;} static inline void setb(uint64_t r){mark[r>>3]|=(uint8_t)(1u<<(r&7));}
static void push(uint64_t r){ if(qt==qc){qc=qc?qc*2:(1u<<20); q=realloc(q,qc*sizeof(uint32_t));} q[qt++]=(uint32_t)r; }
static int stk[16]; static uint64_t nj;
static void jdfs(int d, unsigned used) { // b'de biten J-yolları: stk[n-1]=B, geriye doğru kur
    if (d < 0) { uint64_t r = rank_front(stk); if (!getb(r)) { setb(r); push(r); nj++; } return; }
    unsigned c = J[stk[d + 1]] & ~used;
    while (c) { int w = __builtin_ctz(c); c &= c - 1; stk[d] = w; jdfs(d - 1, used | (1u << w)); }
}
int main(void) {
    int m; if (scanf("%d %d %d", &n, &m, &B) != 3) return 1;
    for (int i = 0; i < m; i++) { int a, b; scanf("%d %d", &a, &b); J[a] |= 1u << b; J[b] |= 1u << a; }
    fact[0] = 1; for (int i = 1; i <= n; i++) fact[i] = fact[i - 1] * i;
    int k = 0; for (int v = 0; v < n; v++) if (v != B) others[k++] = v;
    uint64_t N = fact[n - 1]; mark = calloc(N / 8 + 1, 1);
    stk[n - 1] = B; jdfs(n - 2, 1u << B);
    int p[16], t[16];
    while (qh < qt) {
        unrank_front(q[qh++], p);
        for (int kk = 2; kk < n; kk++) { // ön çevirme: tersi J-kenarı silen hamle
            if (!((J[p[kk - 1]] >> p[kk]) & 1)) continue;
            int mm = 0; for (int i = kk - 1; i >= 0; i--) t[mm++] = p[i]; for (int i = kk; i < n; i++) t[mm++] = p[i];
            uint64_t r = rank_front(t); if (!getb(r)) { setb(r); push(r); }
        }
    }
    printf("n=%d b=%d J_yol(b'de biten)=%llu ulasilan=%llu / %llu %s\n", n, B, (unsigned long long)nj,
           (unsigned long long)qt, (unsigned long long)N, qt == N ? "ONDEN_ZORLAYICI" : "DEGIL");
    return 0;
}
