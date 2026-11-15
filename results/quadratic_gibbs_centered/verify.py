"""Exact finite checks for report.tex. Python 3 standard library only.

All measures, polynomial coefficients, moments, and influences are
Fractions. Only comparisons involving exp/log and fractional powers
use floating-point arithmetic. No finite test proves the uniform theorem.
"""
from fractions import Fraction as F
from itertools import combinations
from math import exp, log, sqrt
from random import Random

RNG = Random(20261114)


def sign(x, i):
    return 1 if x & (1 << i) else -1


def character(x, mask):
    result = 1
    for i in range(mask.bit_length()):
        if mask & (1 << i):
            result *= sign(x, i)
    return result


def atanh_fraction(t):
    return log(float((1 + t) / (1 - t))) / 2


def law(n, terms, fields=None):
    weights = []
    fields = fields or {}
    for x in range(1 << n):
        w = F(1)
        for mask, t in terms.items():
            w *= 1 + t * character(x, mask)
        for i, u in fields.items():
            w *= 1 + u * sign(x, i)
        weights.append(w)
    z = sum(weights)
    return [w / z for w in weights]


def expect(mu, values):
    return sum(w * y for w, y in zip(mu, values))


def poly_values(n, coeff):
    return [sum(a * character(x, mask) for mask, a in coeff.items())
            for x in range(1 << n)]


def moments(mu, values):
    mean = expect(mu, values)
    second = expect(mu, [v * v for v in values])
    return mean, second, second - mean * mean


def local_statistics(n, mu):
    means = [expect(mu, [sign(x, i) for x in range(1 << n)]) for i in range(n)]
    sig2 = [1 - m * m for m in means]
    theta, local_var = [], []
    for i in range(n):
        p = [mu[x | (1 << i)] / (mu[x | (1 << i)] + mu[x & ~(1 << i)])
             for x in range(1 << n)]
        theta.append(p)
        local_var.append([4 * v * (1 - v) for v in p])
    influence_matrix = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                influence_matrix[i][j] = max(abs(theta[i][x] - theta[i][x ^ (1 << j)])
                                             for x in range(1 << n))
    r = max(map(sum, influence_matrix), default=F(0))
    return means, sig2, local_var, r


def influences(n, mu, values, local_var):
    derivatives, flip, pv = [], [], []
    for i in range(n):
        ri = [(values[x | (1 << i)] - values[x & ~(1 << i)]) / 2
              for x in range(1 << n)]
        derivatives.append(ri)
        flip.append(4 * expect(mu, [z * z for z in ri]))
        pv.append(expect(mu, [v * z * z for v, z in zip(local_var[i], ri)]))
    return derivatives, flip, pv


def close_float(lhs, rhs):
    assert float(lhs) <= float(rhs) * (1 + 2e-10) + 1e-40, (lhs, rhs)


def check_positive(n, mu, coeff, interaction_bound):
    raw = poly_values(n, coeff)
    scale = max(map(abs, raw))
    assert scale > 0
    coeff = {s: a / scale for s, a in coeff.items()}
    values = [v / scale for v in raw]
    assert max(map(abs, values)) == 1
    means, sig2, local_var, r = local_statistics(n, mu)
    assert r < 1
    C = 1 / (1 - r)
    D = exp(4 * interaction_bound)
    mean, second, variance = moments(mu, values)
    ri, flip, pv = influences(n, mu, values, local_var)
    assert variance <= C * sum(pv)
    for i in range(n):
        for loc in local_var[i]:
            close_float(sig2[i] / D, loc)
            close_float(loc, D * float(sig2[i]))
        assert flip[i] >= 4 * pv[i]

    a = [coeff.get(1 << i, F(0)) for i in range(n)]
    b = [[F(0) if i == j else coeff.get((1 << i) | (1 << j), F(0))
          for j in range(n)] for i in range(n)]
    centered = [a[i] + sum(b[i][j] * means[j] for j in range(n)) for i in range(n)]
    assert sum(map(abs, centered)) <= 9
    usq = [sig2[i] * centered[i] ** 2 for i in range(n)]
    wsq = {(i, j): sig2[i] * sig2[j] * b[i][j] ** 2
           for i in range(n) for j in range(i + 1, n)}
    power_sum = sum(float(v) ** (2 / 3) for v in usq)
    power_sum += sum(float(v) ** (2 / 3) for v in wsq.values())
    assert power_sum < 36 + 1e-9
    for i in range(n):
        second_ri = expect(mu, [z * z for z in ri[i]])
        assert expect(mu, ri[i]) == centered[i]
        assert second_ri <= centered[i] ** 2 + C * sum(b[i][j] ** 2 * sig2[j] for j in range(n))
        close_float(float(usq[i]) / D, pv[i])
        assert flip[i] >= 4 * usq[i]
        for j in range(n):
            if i == j:
                continue
            assert second_ri >= b[i][j] ** 2 * expect(mu, local_var[j])
            w2 = sig2[i] * sig2[j] * b[i][j] ** 2
            close_float(float(w2) / D ** 2, pv[i])
            close_float(4 * float(w2) / D, flip[i])

    energy = sum(usq) + sum(wsq.values())
    L = 2 * float(C) ** 2 * D
    close_float(variance, L * float(energy))
    m2 = max(usq + list(wsq.values()))
    close_float((float(variance) / (36 * L)) ** 3, m2)
    target_fl = exp(-16 * interaction_bound) * float(1 - r) ** 6 * float(variance) ** 3 / 93312
    target_pv = exp(-20 * interaction_bound) * float(1 - r) ** 6 * float(variance) ** 3 / 373248
    assert any(float(f) + 1e-40 >= target_fl and float(p) + 1e-40 >= target_pv
               for f, p in zip(flip, pv))


def random_poly(n):
    masks = [0] + [1 << i for i in range(n)]
    masks += [(1 << i) | (1 << j) for i in range(n) for j in range(i + 1, n)]
    return {m: F(RNG.randint(-5, 5)) for m in masks}


def check_pairs():
    for m in range(1, 6):
        n = 2 * m
        masks = [3 << (2 * j) for j in range(m)]
        mu = law(n, {s: F(1, 9) for s in masks})
        values = poly_values(n, {0: -F(1, 10), **{s: F(9, 10 * m) for s in masks}})
        assert moments(mu, values) == (0, F(4, 5 * m), F(4, 5 * m))
        assert max(map(abs, values)) == 1
        assert sum(values) / len(values) == -F(1, 10)
        stats = local_statistics(n, mu)
        _, flip, pv = influences(n, mu, values, stats[2])
        assert set(flip) == {F(81, 25 * m * m)}
        assert set(pv) == {F(4, 5 * m * m)}
        opt = poly_values(n, {0: F(80 + m, 80 + 10 * m),
                             **{s: -F(9, 80 + 10 * m) for s in masks}})
        a0 = sum(opt) / len(opt)
        _, norm2, _ = moments(mu, opt)
        assert max(map(abs, opt)) == 1
        assert norm2 / (a0 * a0) == F(80, 80 + m)
        fm = poly_values(n, {s: F(1, m) for s in masks})
        assert moments(mu, fm)[1] / F(1, m) == F(m + 80, 81)
    print("PASS: exact pair-block statistics and sharp (B) extremizers, m=1,...,5")
    for m in (10, 100, 1000, 1000000):
        print(f"  analytic m={m}: lambda_B={F(80,80+m)}, H2 ratio={F(m+80,81)}")


def solve(matrix, rhs):
    a = [list(row) + [v] for row, v in zip(matrix, rhs)]
    n = len(a)
    for i in range(n):
        pivot = next(j for j in range(i, n) if a[j][i])
        a[i], a[pivot] = a[pivot], a[i]
        denominator = a[i][i]
        a[i] = [v / denominator for v in a[i]]
        for j in range(n):
            if j != i:
                factor = a[j][i]
                if factor:
                    a[j] = [x - factor * y for x, y in zip(a[j], a[i])]
    return [row[-1] for row in a]


def check_cycles():
    for n in range(3, 7):
        terms = {(1 << i) | (1 << ((i + 1) % n)): F(1, 25) for i in range(n)}
        mu = law(n, terms)
        masks = [s for s in range(1 << n) if s.bit_count() <= 2]
        moments_chi = {s: expect(mu, [character(x, s) for x in range(1 << n)])
                       for s in range(1 << n)}
        gram = [[moments_chi[s ^ t] for t in masks] for s in masks]
        solution = solve(gram, [F(s == 0) for s in masks])
        lam = 1 / solution[0]
        values = poly_values(n, dict(zip(masks, solution)))
        norm2 = moments(mu, values)[1]
        assert norm2 / solution[0] ** 2 == lam
        check_positive(n, mu, random_poly(n), 2 * atanh_fraction(F(1, 25)))
        print(f"PASS: cycle n={n}, exact Gram solve; best lambda_B={float(lam):.12f}")


def check_odd_arity():
    mu = law(4, {7: F(1, 41), 15: F(1, 41)})
    s = expect(mu, [sign(x, 3) for x in range(16)])
    assert s == F(1, 1681)
    assert 5 * atanh_fraction(F(1, 41)) < 1 / 8
    for m in (2, 3, 4):
        zlaw = law(m, {}, {i: s for i in range(m)})
        count = m * (m - 1) // 2
        coeff = {(1 << i) | (1 << j): F(1, count)
                 for i in range(m) for j in range(i + 1, m)}
        variance = moments(zlaw, poly_values(m, coeff))[2]
        ratio = 1 - s ** 4 + 2 * (m - 2) * s * s * (1 - s * s)
        assert variance / F(1, count) == ratio
    check_positive(4, mu, random_poly(4), 2 * atanh_fraction(F(1, 41)))
    print("PASS: zero-field odd-arity example; E[X4]=1/1681; amplified Gram formula exact")


def pin_law(n, mu, pinned):
    free = [i for i in range(n) if i not in pinned]
    out = []
    for x in range(1 << len(free)):
        old = sum((1 << i) for i, value in pinned.items() if value == 1)
        old += sum((1 << i) for j, i in enumerate(free) if sign(x, j) == 1)
        out.append(mu[old])
    total = sum(out)
    return len(free), [w / total for w in out]


def check_random_cases():
    count = 0
    for n in (3, 4, 5, 6, 7):
        possible = [s for s in range(1 << n) if 2 <= s.bit_count() <= 5]
        for trial in range(6):
            masks = RNG.sample(possible, min(len(possible), 7))
            terms = {s: F(RNG.choice((-1, 1)), 400) for s in masks}
            if trial == 0:
                terms = {}  # Product laws, with arbitrary biases.
            fields = {i: RNG.choice((F(0), F(4, 5), -F(9, 10),
                                     F(10**12-1, 10**12+1), -F(10**12-1, 10**12+1)))
                      for i in range(n)}
            if trial == 1:
                fields = {}
            k = max((sum(abs(atanh_fraction(t)) for s, t in terms.items() if s & (1 << i))
                     for i in range(n)), default=0)
            omega = max((sum((s.bit_count()-1)*abs(atanh_fraction(t))
                             for s, t in terms.items() if s & (1 << i)) for i in range(n)), default=0)
            assert omega <= 1 / 8
            mu = law(n, terms, fields)
            for _ in range(2):
                check_positive(n, mu, random_poly(n), k)
                count += 1
            n2, pinned = pin_law(n, mu, {0: -1, n-1: 1})
            check_positive(n2, pinned, random_poly(n2), k)
            count += 1
    # Beyond omega=1/8: signed pairwise cycles in the Dobrushin region.
    for n in (3, 4, 5, 6):
        terms = {(1 << i) | (1 << ((i+1) % n)): F((-1)**i, 3) for i in range(n)}
        mu = law(n, terms, {0: F(999, 1000), 1: -F(999, 1000)})
        for _ in range(2):
            check_positive(n, mu, random_poly(n), 2 * atanh_fraction(F(1, 3)))
            count += 1
    print(f"PASS: {count} quadratic cases with products, arbitrary fields, signed higher arity, pinnings, and Dobrushin cycles")


if __name__ == "__main__":
    check_pairs()
    check_cycles()
    check_odd_arity()
    check_random_cases()
    constant = exp(-2) * (7/8)**6 / 93312
    print(f"omega <= 1/8: proved flip coefficient is {constant:.12g} times v^3")
    print("All finite checks passed. No independent audit or proof-assistant certification is claimed.")
