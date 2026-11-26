from collections import deque


def paths_graph(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)

    def extend(p):
        if len(p) == n:
            if p[0] < p[-1]:
                yield p
        else:
            for u in adj[p[-1]].difference(p):
                yield from extend(p + (u,))

    paths = [p for i in range(n) for p in extend((i,))]
    lookup = {p: i for i, p in enumerate(paths)}

    def rotations(p):
        for oriented in (p, p[::-1]):
            for k in range(2, n):
                if oriented[k] in adj[oriented[0]]:
                    moved = oriented[:k][::-1] + oriented[k:]
                    yield lookup[min(moved, moved[::-1])]

    nb = [set(rotations(p)) for p in paths]
    return nb


def dist(nb, i):
    q = deque([i])
    d = {i: 0}
    while q:
        i = q.popleft()
        for j in nb[i]:
            if j not in d:
                d[j] = d[i] + 1
                q.append(j)
    return d


p = [0, 1, 7, 8, 9, 4, 3, 2, 6, 5]
nb = paths_graph(10, [(i, (i + 1) % 10) for i in range(10)] + list(zip(p, p[1:])))
left = set(range(len(nb)))
parts = []
while left:
    q = dist(nb, next(iter(left)))
    parts.append(len(q))
    left -= q.keys()
print("example", sorted(parts))
for n in range(4, 19):
    nb = paths_graph(n, [(i, j) for j in range(n) for i in range(j) if j - i <= 2])
    print(
        n, len(nb), max(max(dist(nb, i).values()) for i in range(len(nb))), flush=True
    )

for name, edges in {
    "ladder": [(i, i + 2) for i in range(10)] + [(i, i + 1) for i in range(0, 12, 2)],
    "d13": [(i, i + d) for d in (1, 3) for i in range(12 - d)],
}.items():
    nb = paths_graph(12, edges)
    assert len(dist(nb, 0)) == len(nb)
    print(name, len(nb), "paths; connected")
