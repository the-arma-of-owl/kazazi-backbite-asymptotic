"""Burnside over vertex permutations of graphs of bounded maximum degree.

Between cycles of lengths a and b there are gcd(a,b) edge orbits.
Inside a cycle each distance contributes two to each degree, except a diameter.
Remaining per-vertex degree capacities are carried between cycles.
"""

from math import gcd, comb, factorial
from collections import Counter
from functools import cache


def parts(n, m=1):
    if not n:
        yield ()
    for j in range(m, n + 1):
        for p in parts(n - j, j):
            yield (j,) + p


@cache
def bounded(cycles):
    if not cycles:
        return 1
    a, cap = cycles[-1]
    tail = cycles[:-1]
    choices = Counter()

    def pairs(i, left, out, mult):
        if i == len(tail):
            inside = sum(
                comb((a - 1) // 2, k)
                for k in range((a - 1) // 2 + 1)
                for diam in range(1 + int(a % 2 == 0))
                if 2 * k + diam <= left
            )
            choices[tuple(sorted(out))] += mult * inside
            return
        b, cb = tail[i]
        g = gcd(a, b)
        da = b // g
        db = a // g
        for k in range(1 + min(g, left // da, cb // db)):
            pairs(i + 1, left - k * da, out + [(b, cb - k * db)], mult * comb(g, k))

    pairs(0, cap, [], 1)
    return sum(m * bounded(t) for t, m in choices.items())


for n, d in [(10, 5), (11, 6), (12, 6)]:
    tot = 0
    for p in parts(n):
        z = 1
        for a, k in Counter(p).items():
            z *= a**k * factorial(k)
        tot += factorial(n) // z * bounded(tuple((a, n - 1 - d) for a in p))
    assert tot % factorial(n) == 0
    print(n, d, tot // factorial(n), flush=True)
