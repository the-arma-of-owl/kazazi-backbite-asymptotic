// bbconn.c — Backbite yeniden yapılandırma grafiği R(G)'nin bağlantılılığı.
// Girdi: stdin'den graph6 satırları (ör. geng çıktısı). n <= 16.
// Kullanım: bbconn [-s] [-o] [-v]
//   -s : yayılan kare-yol (P_n^2) içeren grafları atla (Kazazi Tm 1.1 bunları kapsar)
//   -o : yalnızca Ore koşulunu (komşu olmayan her çift için d(u)+d(v) >= n) sağlayanları incele
//   -v : bağlantısız her graf için bileşen boyutlarını yaz
// Çıktı: bağlantısız grafların graph6 kodu + özet.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
typedef uint64_t u64;

static int n;
static unsigned adj[MAXN];

static int parse_g6(const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    int nn = p[0] - 63;
    if (nn < 1 || nn > MAXN) return -1;
    n = nn;
    memset(adj, 0, sizeof adj);
    p++;
    int k = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int byte = p[k / 6] - 63;
            if ((byte >> (5 - k % 6)) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
            k++;
        }
    return n;
}

static int deg(int v) { return __builtin_popcount(adj[v]); }

static int is_ore(void) {
    for (int u = 0; u < n; u++)
        for (int v = u + 1; v < n; v++)
            if (!((adj[u] >> v) & 1) && deg(u) + deg(v) < n) return 0;
    return 1;
}

// --- yayılan kare-yol (v_i ~ v_{i+1}, v_i ~ v_{i+2}) araması ---
static int sq_dfs(int a, int b, unsigned used, int cnt) {
    if (cnt == n) return 1;
    unsigned cand = adj[a] & adj[b] & ~used;
    while (cand) {
        int c = __builtin_ctz(cand); cand &= cand - 1;
        if (sq_dfs(b, c, used | (1u << c), cnt + 1)) return 1;
    }
    return 0;
}
static int has_square_path(void) {
    if (n <= 2) return 1;
    for (int a = 0; a < n; a++) {
        unsigned nb = adj[a];
        while (nb) {
            int b = __builtin_ctz(nb); nb &= nb - 1;
            if (sq_dfs(a, b, (1u << a) | (1u << b), 2)) return 1;
        }
    }
    return 0;
}


// --- yayılan merdiven P_{n/2} x K_2 (n çift) ---
static int lad_dfs(int a, int b, unsigned used, int cnt) {
    if (cnt == n) return 1;
    unsigned ca = adj[a] & ~used;
    while (ca) {
        int a2 = __builtin_ctz(ca); ca &= ca - 1;
        unsigned cb = adj[b] & adj[a2] & ~used & ~(1u << a2);
        while (cb) {
            int b2 = __builtin_ctz(cb); cb &= cb - 1;
            if (lad_dfs(a2, b2, used | (1u << a2) | (1u << b2), cnt + 2)) return 1;
        }
    }
    return 0;
}
static int has_ladder(void) {
    if (n % 2) return 0;
    for (int a = 0; a < n; a++) { unsigned nb = adj[a]; while (nb) { int b = __builtin_ctz(nb); nb &= nb - 1;
        if (lad_dfs(a, b, (1u << a) | (1u << b), 2)) return 1; } }
    return 0;
}
// --- yayılan d13: v_i ~ v_{i+1}, v_i ~ v_{i+3} ---
static int ord13[16];
static int d13_dfs(int d, unsigned used) {
    if (d == n) return 1;
    unsigned c = adj[ord13[d - 1]] & ~used;
    if (d >= 3) c &= adj[ord13[d - 3]];
    while (c) { int w = __builtin_ctz(c); c &= c - 1; ord13[d] = w; if (d13_dfs(d + 1, used | (1u << w))) return 1; }
    return 0;
}
static int has_d13(void) { for (int s = 0; s < n; s++) { ord13[0] = s; if (d13_dfs(1, 1u << s)) return 1; } return 0; }

// --- Hamilton yollarını listele (kanonik yön: ilk tepe < son tepe), kodlar sıralı çıkar ---
static u64 *paths; static size_t npaths, cap;
static int stk[MAXN];
static void push_path(void) {
    if (stk[0] > stk[n - 1]) return;
    u64 code = 0;
    for (int i = 0; i < n; i++) code = (code << 4) | (u64)stk[i];
    if (npaths == cap) { cap = cap ? cap * 2 : (1u << 16); paths = realloc(paths, cap * sizeof(u64)); if (!paths) { perror("realloc"); exit(1); } }
    paths[npaths++] = code;
}
static void hp_dfs(int depth, unsigned used) {
    if (depth == n) { push_path(); return; }
    unsigned cand = adj[stk[depth - 1]] & ~used;
    while (cand) {
        int w = __builtin_ctz(cand); cand &= cand - 1;
        stk[depth] = w;
        hp_dfs(depth + 1, used | (1u << w));
    }
}

static long find_code(u64 c) {
    size_t lo = 0, hi = npaths;
    while (lo < hi) { size_t mid = (lo + hi) / 2; if (paths[mid] < c) lo = mid + 1; else hi = mid; }
    return (lo < npaths && paths[lo] == c) ? (long)lo : -1;
}

static uint32_t *par, *sz;
static uint32_t uf_find(uint32_t x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }
static void uf_union(uint32_t a, uint32_t b) {
    a = uf_find(a); b = uf_find(b);
    if (a == b) return;
    if (sz[a] < sz[b]) { uint32_t t = a; a = b; b = t; }
    par[b] = a; sz[a] += sz[b];
}

static u64 encode_canon(const int *q) {
    u64 c = 0;
    if (q[0] < q[n - 1]) for (int i = 0; i < n; i++) c = (c << 4) | (u64)q[i];
    else for (int i = n - 1; i >= 0; i--) c = (c << 4) | (u64)q[i];
    return c;
}
static void decode(u64 c, int *q) { for (int i = n - 1; i >= 0; i--) { q[i] = (int)(c & 15); c >>= 4; } }

// R(G) bileşen sayısı; npaths'i de doldurur.
static long components(void) {
    npaths = 0;
    if (n == 1) { npaths = 1; return 1; }
    for (int s = 0; s < n; s++) { stk[0] = s; hp_dfs(1, 1u << s); }
    if (npaths == 0) return 0;
    par = realloc(par, npaths * sizeof(uint32_t));
    sz = realloc(sz, npaths * sizeof(uint32_t));
    for (size_t i = 0; i < npaths; i++) { par[i] = (uint32_t)i; sz[i] = 1; }
    int q[MAXN], r[MAXN], t[MAXN];
    for (size_t idx = 0; idx < npaths; idx++) {
        decode(paths[idx], q);
        for (int side = 0; side < 2; side++) {
            if (side == 0) memcpy(r, q, sizeof(int) * n);
            else for (int i = 0; i < n; i++) r[i] = q[n - 1 - i];
            int w0 = r[0];
            // backbite: uç w0, hedef r[k] (k>=2), sonuç r[k-1..0], r[k..n-1]
            for (int k = 2; k < n; k++) {
                if (!((adj[w0] >> r[k]) & 1)) continue;
                int m = 0;
                for (int i = k - 1; i >= 0; i--) t[m++] = r[i];
                for (int i = k; i < n; i++) t[m++] = r[i];
                long j = find_code(encode_canon(t));
                if (j < 0) { fprintf(stderr, "HATA: komşu yol bulunamadı\n"); exit(2); }
                uf_union((uint32_t)idx, (uint32_t)j);
            }
        }
    }
    long comps = 0;
    for (size_t i = 0; i < npaths; i++) if (uf_find((uint32_t)i) == i) comps++;
    return comps;
}

// Kapanış testi: komşu olmayan u,v için d(u)+d(v) >= T ise
//   bağ(G+uv) => bağ(G)   ve   bağ(G) => bağ(G+uv)   ihlallerini say.
static void closure_test(int T, const char *line, long *viol_back, long *viol_fwd, long *pairs) {
    long cG = components();
    size_t pG = npaths;
    unsigned save[MAXN]; memcpy(save, adj, sizeof adj);
    for (int u = 0; u < n; u++)
        for (int v = u + 1; v < n; v++) {
            if ((save[u] >> v) & 1) continue;
            int du = __builtin_popcount(save[u]), dv = __builtin_popcount(save[v]);
            if (du + dv < T) continue;
            memcpy(adj, save, sizeof adj);
            adj[u] |= 1u << v; adj[v] |= 1u << u;
            long cH = components();
            (*pairs)++;
            if (cH == 1 && cG > 1) {
                (*viol_back)++;
                printf("GERI_IHLAL %s u=%d v=%d du=%d dv=%d bilesen(G)=%ld yol(G)=%zu\n", line, u, v, du, dv, cG, pG);
            }
            if (cG == 1 && cH > 1) {
                (*viol_fwd)++;
                printf("ILERI_IHLAL %s u=%d v=%d du=%d dv=%d bilesen(G+uv)=%ld\n", line, u, v, du, dv, cH);
            }
            if ((cG == 0) != (cH == 0)) printf("HP_FARKI %s u=%d v=%d\n", line, u, v);
        }
    memcpy(adj, save, sizeof adj);
}

int main(int argc, char **argv) {
    int skip_sq = 0, only_ore = 0, verbose = 0, closureT = -1, skip_force12 = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-s")) skip_sq = 1;
        else if (!strcmp(argv[i], "-o")) only_ore = 1;
        else if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "-F")) skip_force12 = 1;
        else if (!strcmp(argv[i], "-T")) { char l[256]; while (fgets(l, sizeof l, stdin)) { l[strcspn(l, "\r\n")] = 0; if (!l[0] || l[0] == '>') continue; if (parse_g6(l) < 0) continue; printf("%s %d %d %d\n", l, has_ladder(), has_d13(), has_square_path()); } return 0; }
        else if (!strcmp(argv[i], "-k") && i + 1 < argc) closureT = atoi(argv[++i]);
    }
    if (closureT >= 0) {
        // T değeri n'ye göreli: T = n + closureT - 100 (ör. -k 100 => T=n, -k 101 => T=n+1, -k 99 => T=n-1)
        char line[256]; long vb = 0, vf = 0, pairs = 0, graphs = 0;
        while (fgets(line, sizeof line, stdin)) {
            line[strcspn(line, "\r\n")] = 0;
            if (!line[0] || line[0] == '>') continue;
            if (parse_g6(line) < 0) continue;
            graphs++;
            closure_test(n + closureT - 100, line, &vb, &vf, &pairs);
            fflush(stdout);
        }
        printf("KAPANIS_OZET graf=%ld cift=%ld geri_ihlal=%ld ileri_ihlal=%ld\n", graphs, pairs, vb, vf);
        return 0;
    }
    char line[256];
    long total = 0, nonore = 0, sqskip = 0, nohp = 0, checked = 0, bad = 0;
    size_t maxpaths = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0] || line[0] == '>') continue;
        if (parse_g6(line) < 0) { fprintf(stderr, "atlandı (n>16): %s\n", line); continue; }
        total++;
        if (only_ore && !is_ore()) { nonore++; continue; }
        if (skip_sq && has_square_path()) { sqskip++; continue; }
        if (skip_force12 && n == 12 && (has_ladder() || has_d13())) { sqskip++; continue; }
        long c = components();
        if (npaths > maxpaths) maxpaths = npaths;
        if (c == 0) { nohp++; continue; }
        checked++;
        if (c > 1) {
            bad++;
            int mind = n; for (int v = 0; v < n; v++) if (deg(v) < mind) mind = deg(v);
            printf("BAGLANTISIZ %s n=%d delta=%d yol=%zu bilesen=%ld\n", line, n, mind, npaths, c);
            if (verbose) {
                // bileşen boyutları
                printf("  boyutlar:");
                for (size_t i = 0; i < npaths; i++) if (uf_find((uint32_t)i) == i) printf(" %u", sz[i]);
                printf("\n");
            }
            fflush(stdout);
        }
    }
    printf("OZET toplam=%ld ore_degil=%ld kare_yol_atlanan=%ld hamilton_yolu_yok=%ld incelenen=%ld baglantisiz=%ld en_cok_yol=%zu\n",
           total, nonore, sqskip, nohp, checked, bad, maxpaths);
    return 0;
}
