#include <algorithm>
#include <array>
#include <cassert>
#include <cstdio>
#include <cstring>
using namespace std;
using P = array<unsigned char, 12>;
static bool adj[12][12];
static int N;
// Can we decrease the number of edges outside J after at most dep neutral
// rotations?
static bool desc(P &p, int dep) {
  for (int k = 2; k < N; k++)
    if (adj[p[0]][p[k]] && !adj[p[k - 1]][p[k]])
      return true;
  for (int k = 0; k < N - 2; k++)
    if (adj[p[N - 1]][p[k]] && !adj[p[k]][p[k + 1]])
      return true;
  if (dep) {
    for (int k = 2; k < N; k++)
      if (adj[p[0]][p[k]]) {
        reverse(p.begin(), p.begin() + k);
        bool ok = desc(p, dep - 1);
        reverse(p.begin(), p.begin() + k);
        if (ok)
          return true;
      }
    for (int k = 0; k < N - 2; k++)
      if (adj[p[N - 1]][p[k]]) {
        reverse(p.begin() + k + 1, p.begin() + N);
        bool ok = desc(p, dep - 1);
        reverse(p.begin() + k + 1, p.begin() + N);
        if (ok)
          return true;
      }
  }
  return false;
}
int main() {
  int m;
  if (scanf("%d%d", &N, &m) != 2 || N < 3 || N > 12 || m < 0 ||
      m > N * (N - 1) / 2)
    return 2;
  for (int i = 0, a, b; i < m; i++) {
    if (scanf("%d%d", &a, &b) != 2 || a < 0 || a >= N || b < 0 || b >= N ||
        a == b)
      return 2;
    adj[a][b] = adj[b][a] = true;
  }
  P p{};
  for (int i = 0; i < N; i++)
    p[i] = i;
  unsigned long long paths = 0, orders = 0;
  int maxdep = 0;
  do {
    if (p[0] > p[N - 1])
      continue;
    orders++;
    if (desc(p, 0))
      continue;
    bool good = true;
    for (int j = 1; j < N; j++)
      if (!adj[p[j - 1]][p[j]]) {
        good = false;
        break;
      }
    if (good) {
      paths++;
      continue;
    }
    int dep = 1;
    while (!desc(p, dep)) {
      if (dep++ >= 9) {
        puts("inconclusive");
        return 1;
      }
    }
    maxdep = max(dep, maxdep);
  } while (next_permutation(p.begin(), p.begin() + N));
  printf("orders %llu paths %llu; all others have a descending move after <=%d "
         "neutral moves\n",
         orders, paths, maxdep);
}
