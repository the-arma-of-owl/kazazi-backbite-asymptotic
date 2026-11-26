// forcing.c — Bir J iskeleti "zorlayıcı" mı?
// Ölçüt (F): (i) J'nin her Hamilton yolu birbirine bağlı (R(J) bağlantılı) ve
//            (ii) [n] üzerindeki HER permütasyon P'den, yalnızca J-kenarı EKLEYEN
//                 backbite'larla J'nin bir Hamilton yoluna ulaşılabilir.
// (F) doğruysa J'yi yayılan alt graf olarak içeren her G için R(G) bağlantılıdır:
// G ⊇ J ise P ∈ HP(G)'den J-ekleyen hamleler G içinde kalır ve J-yoluna varır.
// (ii) ters BFS ile denetlenir: J-yollarından başlayıp J-kenarı SİLEN backbite'larla
// (K_n içinde) ulaşılan permütasyonlar işaretlenir; hepsi işaretlenmeli.
// Girdi: stdin'den "n m" ve m kenar "a b" (0-tabanlı). n <= 12.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int n;
static unsigned J[16];
static uint64_t fact[16];

static uint64_t rank_perm(const int *p) {
    // Lehmer kodu
    uint64_t r = 0; unsigned used = 0;
    for (int i = 0; i < n; i++) {
        int smaller = __builtin_popcount(((1u << p[i]) - 1) & ~used);
        r += (uint64_t)smaller * fact[n - 1 - i];
        used |= 1u << p[i];
    }
    return r;
}
static void unrank_perm(uint64_t r, int *p) {
    unsigned used = 0;
    for (int i = 0; i < n; i++) {
        uint64_t f = fact[n - 1 - i];
        int k = (int)(r / f); r %= f;
        for (int v = 0; v < n; v++) if (!((used >> v) & 1)) { if (k == 0) { p[i] = v; used |= 1u << v; break; } k--; }
    }
}
static uint64_t canon_rank(const int *p) {
    if (p[0] < p[n - 1]) return rank_perm(p);
    int q[16]; for (int i = 0; i < n; i++) q[i] = p[n - 1 - i];
    return rank_perm(q);
}

static uint8_t *mark;   // bitset, kanonik yönler
static uint32_t *queue; static uint64_t qh, qt, qcap;
static inline int getb(uint64_t r) { return (mark[r >> 3] >> (r & 7)) & 1; }
static inline void setb(uint64_t r) { mark[r >> 3] |= (uint8_t)(1u << (r & 7)); }
static void push(uint64_t r) {
    if (qt == qcap) { qcap = qcap ? qcap * 2 : (1u << 20); queue = realloc(queue, qcap * sizeof(uint32_t)); if (!queue) { perror("realloc"); exit(1); } }
    queue[qt++] = (uint32_t)r;
}

// J'nin Hamilton yollarını üret, işaretle, kuyruğa koy
static int stk[16]; static uint64_t njpaths;
static void jdfs(int d, unsigned used) {
    if (d == n) {
        if (stk[0] < stk[n - 1]) { uint64_t r = rank_perm(stk); if (!getb(r)) { setb(r); push(r); njpaths++; } }
        return;
    }
    unsigned c = J[stk[d - 1]] & ~used;
    while (c) { int w = __builtin_ctz(c); c &= c - 1; stk[d] = w; jdfs(d + 1, used | (1u << w)); }
}

int main(void) {
    int m;
    if (scanf("%d %d", &n, &m) != 2 || n < 3 || n > 12) { fprintf(stderr, "girdi hatası (3<=n<=12)\n"); return 1; }
    for (int i = 0; i < m; i++) { int a, b; if (scanf("%d %d", &a, &b) != 2) return 1; J[a] |= 1u << b; J[b] |= 1u << a; }
    fact[0] = 1; for (int i = 1; i <= n; i++) fact[i] = fact[i - 1] * i;
    uint64_t N = fact[n];
    mark = calloc(N / 8 + 1, 1);
    for (int s = 0; s < n; s++) { stk[0] = s; jdfs(1, 1u << s); }
    if (njpaths == 0) { printf("J'nin Hamilton yolu yok\n"); return 0; }
    // ters BFS: J-kenarı silen backbite'lar (K_n'de)
    int p[16], r[16], t[16];
    while (qh < qt) {
        uint64_t cur = queue[qh++];
        unrank_perm(cur, p);
        for (int side = 0; side < 2; side++) {
            if (side == 0) memcpy(r, p, sizeof(int) * n); else for (int i = 0; i < n; i++) r[i] = p[n - 1 - i];
            for (int k = 2; k < n; k++) {
                // bb(r0, rk): siler {r[k-1], r[k]}, ekler {r0, rk}
                if (!((J[r[k - 1]] >> r[k]) & 1)) continue;   // silinen kenar J'de olmalı
                int mm = 0;
                for (int i = k - 1; i >= 0; i--) t[mm++] = r[i];
                for (int i = k; i < n; i++) t[mm++] = r[i];
                uint64_t cr = canon_rank(t);
                if (!getb(cr)) { setb(cr); push(cr); }
            }
        }
    }
    uint64_t total = N / 2, reached = qt;
    printf("n=%d J_yol=%llu ulasilan=%llu / %llu  %s\n", n, (unsigned long long)njpaths,
           (unsigned long long)reached, (unsigned long long)total, reached == total ? "ZORLAYICI(ii)" : "DEGIL(ii)");
    if (reached != total) {
        // örnek: ulaşılamayan bir permütasyon
        for (uint64_t x = 0; x < N; x++) {
            int q[16]; unrank_perm(x, q);
            if (q[0] > q[n - 1]) continue;
            if (!getb(x)) { printf("ornek_ulasilamayan:"); for (int i = 0; i < n; i++) printf(" %d", q[i]); printf("\n"); if (!getenv("HEPSI")) break; }
        }
    }
    return 0;
}
