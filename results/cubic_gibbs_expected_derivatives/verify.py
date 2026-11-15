"""Reproducible finite checks for report.tex; Python 3 standard library.

Exact Fraction arithmetic checks moments and every energy/extraction
inequality. Fractional coefficient norms and square-root-scaled generator
evaluations use floats. These checks do not replace the analytic proof.
Run from any directory: python3 /path/to/this/verify.py
"""
from fractions import Fraction as F
from itertools import product
from math import exp, factorial, prod, sqrt
from pathlib import Path
from random import Random
import importlib.util
import sys

sys.dont_write_bytecode = True
HELPER = Path(__file__).resolve().parents[1] / "quadratic_gibbs_centered" / "verify.py"
spec = importlib.util.spec_from_file_location("quadratic_helpers", HELPER)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
law, expect, moments = base.law, base.expect, base.moments
poly_values, sign = base.poly_values, base.sign
local_statistics, influences = base.local_statistics, base.influences
RNG = Random(2026111403)
B = 1024 * 26 ** 1.5
B4 = 1024 ** 4 * 26 ** 6


def subsets(mask):
    result = mask
    while True:
        yield result
        if result == 0:
            return
        result = (result - 1) & mask


def coordinates(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]


def polynomial_at(coeff, point):
    return sum(a * prod(point[i] for i in coordinates(s)) for s, a in coeff.items())


def derivative(values, n, mask):
    result = values
    for i in coordinates(mask):
        result = [(result[x | (1 << i)] - result[x & ~(1 << i)]) / 2
                  for x in range(1 << n)]
    return result


def exact_D(n, terms):
    return max(prod(((1 + abs(t)) / (1 - abs(t))) ** 2
                    for s, t in terms.items() if s & (1 << i))
               for i in range(n))


def random_poly(n, degree=3):
    return {s: F(RNG.randint(-7, 7)) for s in range(1 << n)
            if s.bit_count() <= degree}


def check_generator(n, mu, coeff, means_derivative, sig2):
    # Rational shifts validate the polynomial identity independently of
    # any numerical square roots. Include vertices and interior points.
    shifts = [F(1, 1 + (i % 3)) for i in range(n)]
    coefficients = {s: e * prod(shifts[i] for i in coordinates(s))
                    for s, e in means_derivative.items()}
    for trial in range(4):
        z = [F(RNG.choice((-1, 1))) if trial < 2 else F(RNG.randint(-3, 3), 3)
             for _ in range(n)]
        direct = expect(mu, [polynomial_at(coeff, [sign(x, i) + shifts[i] * z[i]
                                                  for i in range(n)])
                             for x in range(1 << n)])
        expanded = polynomial_at(coefficients, z)
        assert direct == expanded
        assert abs(direct) <= 26

    sigma = [sqrt(float(s)) for s in sig2]
    weighted = {s: float(e) * prod(sigma[i] for i in coordinates(s))
                for s, e in means_derivative.items()}
    z = [RNG.choice((-1, 1)) for _ in range(n)]
    direct = sum(float(w) * polynomial_at(
        coeff, [sign(x, i) + sigma[i] * z[i] for i in range(n)])
                 for x, w in enumerate(mu))
    expanded = polynomial_at(weighted, z)
    assert abs(direct - expanded) <= 1e-10
    assert abs(expanded) <= 26 + 1e-10


def check_case(n, mu, coeff, D, degree=3, generator=True):
    raw = poly_values(n, coeff)
    scale = max(map(abs, raw))
    assert scale > 0
    coeff = {s: a / scale for s, a in coeff.items()}
    values = [v / scale for v in raw]
    assert max(map(abs, values)) == 1
    means, sig2, local_var, r = local_statistics(n, mu)
    assert r < 1
    C = 1 / (1 - r)
    for i in range(n):
        for loc in local_var[i]:
            assert sig2[i] / D <= loc <= D * sig2[i]

    masks = [s for s in range(1 << n) if s.bit_count() <= degree]
    derivatives = {s: derivative(values, n, s) for s in masks}
    dmeans, seconds, variances = {}, {}, {}
    for s in masks:
        dmeans[s], seconds[s], variances[s] = moments(mu, derivatives[s])
        rhs = F(0)
        for i in range(n):
            if s & (1 << i) or s.bit_count() == degree:
                continue
            nxt = s | (1 << i)
            contribution = expect(mu, [v * z * z
                                      for v, z in zip(local_var[i], derivatives[nxt])])
            rhs += contribution
            # Conditional variance lower bound, applied under original mu.
            assert seconds[s] >= contribution
            assert contribution >= sig2[i] * moments(mu, derivatives[nxt])[1] / D
        assert variances[s] <= C * rhs

    a2 = {s: prod(sig2[i] for i in coordinates(s)) * dmeans[s] ** 2
          for s in masks if s}
    energy = sum(a2.values())
    weighted_energy = sum(
        factorial(s.bit_count()) * C ** s.bit_count()
        * D ** min(s.bit_count(), degree - 1) * value
        for s, value in a2.items())
    L = factorial(degree) * C ** degree * D ** (degree - 1)
    assert variances[0] <= weighted_energy <= L * energy

    _, flip, pv = influences(n, mu, values, local_var)
    for s, value in a2.items():
        k = s.bit_count()
        for i in coordinates(s):
            assert flip[i] >= 4 * value / D ** (k - 1)
            assert pv[i] >= value / D ** k
            assert flip[i] >= 4 * pv[i]

    if degree <= 3:
        coefficient_sum = sum(float(value) ** 0.75 for value in a2.values())
        assert coefficient_sum <= B * (1 + 1e-12)
        # The final bound uses B^4, an integer, and is checked exactly.
        L3 = 6 * C ** 3 * D ** 2
        s = max(a2, key=a2.get)
        i = coordinates(s)[0]
        lower_M2 = (variances[0] / L3) ** 4 / B4
        assert a2[s] >= lower_M2
        assert flip[i] >= 4 * lower_M2 / D ** 2
        assert pv[i] >= lower_M2 / D ** 3
        if generator:
            check_generator(n, mu, coeff, dmeans, sig2)
    return r


def check_interpolation():
    nodes = [F(-1), F(-1, 2), F(1, 2), F(1)]
    weights = [prod((2 - y) / (x - y) for y in nodes if y != x) for x in nodes]
    assert weights == [F(-5, 2), F(6), F(-10), F(15, 2)]
    assert sum(map(abs, weights)) == 26
    for degree in range(4):
        assert sum(w * x ** degree for w, x in zip(weights, nodes)) == 2 ** degree
    print("PASS: exact cubic interpolation identity and absolute weight sum 26", flush=True)


def check_pair_obstruction():
    rho = F(1, 9)
    D = ((1 + rho) / (1 - rho)) ** 2
    for m in range(1, 5):
        n = 2 * m + 1
        pairs = [3 << (1 + 2 * j) for j in range(m)]
        mu = law(n, {s: rho for s in pairs})
        coeff = {s | 1: F(1, m) for s in pairs}
        values = poly_values(n, coeff)
        variance = rho ** 2 + (1 - rho ** 2) / m
        assert max(map(abs, values)) == 1
        assert moments(mu, values) == (0, variance, variance)
        assert sum(a * a for a in coeff.values()) == F(1, m)
        means, sig2, lv, r = local_statistics(n, mu)
        assert means == [0] * n and sig2 == [1] * n and r == rho
        _, flip, pv = influences(n, mu, values, lv)
        assert flip[0] == 4 * variance and pv[0] == variance
        assert set(flip[1:]) == {F(4, m * m)}
        assert set(pv[1:]) == {(1 - rho ** 2) / (m * m)}
        dmeans = {s: expect(mu, derivative(values, n, s))
                  for s in range(1 << n) if s.bit_count() <= 3}
        nonzero = {s: value for s, value in dmeans.items() if value}
        assert nonzero == {1: rho, **coeff}
        assert sum(v * v for v in nonzero.values()) == rho ** 2 + F(1, m)
        check_case(n, mu, coeff, D, generator=(m <= 2))
    print("PASS: exact pair-block cubics m=1,...,4, including generator and physical influences", flush=True)
    for m in (10, 100, 1000, 1000000):
        ratio = m * rho ** 2 + 1 - rho ** 2
        print(f"  analytic m={m}: old Gram ratio={ratio}; expected derivative a_{{0}}={rho}", flush=True)


def check_array_bound():
    # Finite independent-sign moment checks for the scalar coefficient proof.
    for _ in range(20):
        a = [[F(RNG.randint(-5, 5)) for _ in range(3)] for _ in range(3)]
        values = [sum(a[j][k] * y[j] * z[k] for j in range(3) for k in range(3))
                  for y in product((-1, 1), repeat=3)
                  for z in product((-1, 1), repeat=3)]
        l2sq = sum(v * v for v in values) / len(values)
        l4 = sum(v ** 4 for v in values) / len(values)
        l1 = sum(map(abs, values)) / len(values)
        assert l2sq == sum(v * v for row in a for v in row)
        assert l4 <= 9 * l2sq ** 2
        assert l2sq <= 9 * l1 ** 2
    print("PASS: 20 exact decoupled bilinear moment/L1 checks", flush=True)


def check_general_cases():
    count = 0
    for n in range(3, 7):
        products = [
            {},
            {i: F((-1) ** i, 3) for i in range(n)},
            {i: (-1) ** i * (1 - F(1, 10 ** 12)) for i in range(n)},
        ]
        for fields in products:
            mu = law(n, {}, fields)
            for _ in range(2):
                check_case(n, mu, random_poly(n), F(1))
                count += 1

        for _ in range(3):
            eligible = [s for s in range(1 << n) if 2 <= s.bit_count() <= min(n, 5)]
            chosen = RNG.sample(eligible, min(len(eligible), n + 2))
            terms = {s: F(RNG.choice((-1, 1)), 300) for s in chosen}
            fields = {i: RNG.choice((F(0), F(2, 3), -F(7, 9), 1 - F(1, 10 ** 12)))
                      for i in range(n)}
            mu = law(n, terms, fields)
            D = exact_D(n, terms)
            for _ in range(2):
                check_case(n, mu, random_poly(n), D)
                count += 1
            # Condition exactly, then retain the original valid upper D.
            n2, pinned = base.pin_law(n, mu, {0: -1})
            old_r = local_statistics(n, mu)[3]
            new_r = check_case(n2, pinned, random_poly(n2), D)
            assert new_r <= old_r
            count += 1

        # Signed cycles beyond omega=1/8; coupling Dobrushin norm <=2/3.
        terms = {(1 << i) | (1 << ((i + 1) % n)): F((-1) ** i, 3)
                 for i in range(n)}
        mu = law(n, terms, {0: F(999, 1000), 1: -F(999, 1000)})
        for _ in range(2):
            check_case(n, mu, random_poly(n), exact_D(n, terms))
            count += 1

    # Explicit zero-field odd-arity block with a nonzero one-site mean.
    terms = {7: F(1, 41), 15: F(1, 41)}
    mu = law(4, terms)
    assert local_statistics(4, mu)[0][3] == F(1, 1681)
    check_case(4, mu, random_poly(4), exact_D(4, terms))
    count += 1
    print(f"PASS: {count} cubic cases: products, near-degenerate fields, signed hyperedges, pinnings, odd arity, Dobrushin cycles", flush=True)

    higher = 0
    for n, degree in ((4, 1), (4, 2), (4, 4), (5, 4), (5, 5), (6, 4)):
        terms = {(1 << n) - 1: F(-1, 40), 3: F(1, 30)}
        mu = law(n, terms, {0: F(9, 10), 1: -F(3, 4)})
        check_case(n, mu, random_poly(n, degree), exact_D(n, terms), degree=degree)
        higher += 1
    print(f"PASS: {higher} additional exact energy-recursion and derivative-extraction cases at degrees 1,2,4,5", flush=True)


if __name__ == "__main__":
    check_interpolation()
    check_pair_obstruction()
    check_array_bound()
    check_general_cases()
    constant = exp(-5) * (7 / 8) ** 12 / (324 * B4)
    print(f"B = 1024 * 26^(3/2) = {B:.12g}")
    print(f"omega <= 1/8: proved cubic flip coefficient = {constant:.12g} times v^4")
    print("All finite checks passed. The analytic proof, not these tests, gives dimension uniformity.")
