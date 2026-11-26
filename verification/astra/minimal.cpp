#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
using namespace std;
constexpr int N = 12, D = 6;
int h, l, g[N], req[N], column[N], deg[N], pat[3][N], order[N];
long long tested = 0, tot = 0;
// Test each of the three fixed spanning patterns by explicitly embedding its
// vertices.
int countbits(int x) { return __builtin_popcount(x); }
bool contains(int p, int at, int used) {
  if (at == N)
    return true;
  int avail = ((1 << N) - 1) ^ used;
  for (int b = pat[p][at]; b; b &= b - 1)
    avail &= g[order[__builtin_ctz(b)]];
  for (; avail; avail &= avail - 1) {
    int x = __builtin_ctz(avail);
    order[at] = x;
    if (contains(p, at + 1, used | (1 << x)))
      return true;
  }
  return false;
}
void patterns() {
  for (int i = 1; i < N; i++) {
    pat[0][i] = (i % 2 ? (1 << (i - 1)) : 0) | (i >= 2 ? (1 << (i - 2)) : 0);
    pat[1][i] = (1 << (i - 1)) | (i >= 2 ? (1 << (i - 2)) : 0);
    pat[2][i] = (1 << (i - 1)) | (i >= 3 ? (1 << (i - 3)) : 0);
  }
}
// Low vertex i needs exactly req[i] neighbours among the high vertices.
// Partially identical high columns can be ordered lexicographically by their
// next bit.
void assign(int i) {
  if (i == l) {
    ++tested;
    if (!contains(0, 0, 0) && !contains(1, 0, 0) && !contains(2, 0, 0)) {
      puts("missing skeleton");
      exit(1);
    }
    return;
  }
  for (int m = 0; m < (1 << h); m++) {
    if (countbits(m) != req[i])
      continue;
    bool ok = true;
    for (int j = 0; j < h; j++) {
      int bit = (m >> j) & 1;
      if (deg[j] + bit + l - 1 - i < D + 1)
        ok = false;
      if (j && column[j] == column[j - 1] && bit > ((m >> (j - 1)) & 1))
        ok = false;
    }
    if (!ok)
      continue;
    g[i] |= m << l;
    for (int j = 0; j < h; j++) {
      int b = (m >> j) & 1;
      column[j] = 2 * column[j] + b;
      deg[j] += b;
      g[l + j] |= b << i;
    }
    assign(i + 1);
    for (int j = 0; j < h; j++) {
      int b = (m >> j) & 1;
      column[j] /= 2;
      deg[j] -= b;
      g[l + j] &= ~(1 << i);
    }
    g[i] &= (1 << l) - 1;
  }
}
int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  h = atoi(argv[1]);
  if (h < 0 || h > 5)
    return 2;
  l = N - h;
  patterns();
  char line[100];
  while (fgets(line, sizeof(line), stdin)) {
    if (line[0] - 63 != l)
      return 2;
    fill(g, g + N, 0);
    int b = 0;
    for (int v = 1; v < l; v++)
      for (int u = 0; u < v; u++, b++)
        if ((line[1 + b / 6] - 63) & (1 << (5 - b % 6))) {
          g[v] |= 1 << u;
          g[u] |= 1 << v;
        }
    for (int i = 0; i < l; i++)
      req[i] = D - countbits(g[i]);
    ++tot;
    assign(0);
  }
  printf("high=%d low_input=%lld completions=%lld all covered\n", h, tot,
         tested);
}
