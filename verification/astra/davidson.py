"""Independent exact checks of the polynomial and the K=78,79 certificates."""

import gzip
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

A = [2, 2, 1, -1, -2, -1, -1, -1, -2, -1, 1, 2, 2]
D = 12
L = 68
T = tuple(t for t in range(-sum(map(abs, A)), sum(map(abs, A)) + 1) if t % 6 == 3)
root = Path(sys.argv[1]) / "certificate"
x, y = sp.symbols("x y")
F = y * (y**2 - 4) * (y + 1) * (2 * y**2 - 3) + 1
f = sum(v * x**i for i, v in enumerate(A))
assert sp.cancel(x**6 * F.subs(y, x + 1 / x) - f) == 0
assert sp.Poly(f, x).is_irreducible
assert sp.Poly(F, y).count_roots(-2, 2) == 6
assert F.subs(y, -2) == F.subs(y, 2) == 1
assert sum(A) == 1
with (root / "fB_K78_feasible_cert.json").open() as data:
    witness = json.load(data)
assert witness["f"] == A
sigma = list(map(Fraction, witness["sigma0"]))
for j, t in enumerate(witness["tau"]):
    assert t in T
    sigma.append((t - sum(a * sigma[j + i] for i, a in enumerate(A[:-1]))) / 2)
assert len(sigma) == 79 and max(map(abs, sigma)) <= 1
print("K=78, max |sigma| =", float(max(map(abs, sigma))), flush=True)

# Use one common binary scale for affine coefficients at every tree level.
# At depth j, c_j = (linear[j] dot x + constant_j) / scale.
scale = 2**L
linear = []
seq = [[scale * (i == k) for k in range(D)] for i in range(D)]
for j in range(L):
    row = [sum(a * seq[j + i][k] for i, a in enumerate(A[:-1])) for k in range(D)]
    linear.append(row)
    assert all(v % 2 == 0 for v in row)
    seq.append([-v // 2 for v in row])

tree = {}
with gzip.open(root / "proof_fB_L68.jsonl.gz", "rt") as data:
    for line in data:
        node = json.loads(line)
        w = tuple(node["w"])
        assert w not in tree and node["t"] == "I"
        tree[w] = node


def upper(sign, weights, w, constants):
    """Certified bound for sign*c_j using the cube and earlier slabs."""
    weights = {int(i): Fraction(q) for i, q in weights.items()}
    assert all(0 <= i < len(w) for i in weights)
    den = math.lcm(*(q.denominator for q in weights.values()))
    assert den > 0
    coeffs = [sign * den * v for v in linear[len(w)]]
    offset = sign * den * constants[-1]
    for i, q in weights.items():
        m = q.numerator * (den // q.denominator)
        offset += scale * (m * w[i] + 2 * abs(m)) - m * constants[i]
        for k, v in enumerate(linear[i]):
            coeffs[k] -= m * v
    return Fraction(offset + sum(map(abs, coeffs)), den * scale)


stack = [((), [0] * D, [])]
seen = maxdepth = 0
while stack:
    w, sigma_constants, previous = stack.pop()
    j = len(w)
    assert j < L
    node = tree[w]
    seen += 1
    maxdepth = max(maxdepth, j)
    c = sum(a * sigma_constants[j + i] for i, a in enumerate(A[:-1]))
    constants = previous + [c]
    low = -upper(-1, node["yl"], w, constants)
    high = upper(1, node["yu"], w, constants)
    for t in T:
        if (j or t > 0) and low <= t + 2 and t - 2 <= high:
            assert (scale * t - c) % 2 == 0
            stack.append(
                (w + (t,), sigma_constants + [(scale * t - c) // 2], constants)
            )
assert seen == len(tree)
print("K=79, certified nodes =", seen, "max depth =", maxdepth)
