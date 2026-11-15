"""Supplementary finite checks for the Taylor heat-bath map construction.

Run with Python 3; only the standard library is required. These checks
do not prove the uniform theorem. The analytic proof is in
notes/high_temperature/classical/07_dobrushin_attempt.tex.
"""

from decimal import Decimal as D, getcontext
from fractions import Fraction
from itertools import product

getcontext().prec = 100
ORDER = 96
TOL = D("1e-60")


def tanh(x):
    z = (2 * x).exp()
    return (z - 1) / (z + 1)


def sincos(x):
    s, c, st, ct = x, D(1), x, D(1)
    for j in range(1, 70):
        st *= -x * x / D((2 * j) * (2 * j + 1))
        ct *= -x * x / D((2 * j - 1) * (2 * j))
        s += st
        c += ct
    return s, c


def coefficients(b):
    # y' = 1-y^2, y(0) = tanh(b).
    out = [tanh(b)]
    for j in range(ORDER):
        out.append((D(j == 0) - sum(out[v] * out[j-v]
                                   for v in range(j + 1))) / (j + 1))
    return out


def check_map(couplings, b):
    n = len(couplings)
    k = sum(abs(a) for a in couplings)
    coeff = coefficients(b)
    r = coeff[0]
    mass, signed_cost = {}, {}
    power = {0: D(1)}
    total_nonconstant = D(0)
    proxy_cost = D(0)
    for ell in range(1, ORDER + 1):
        nxt = {}
        for mask, weight in power.items():
            for j, a in enumerate(couplings):
                new_mask = mask ^ (1 << j)
                nxt[new_mask] = nxt.get(new_mask, D(0)) + weight * a
        power = nxt
        for mask, weight in power.items():
            signed_weight = coeff[ell] * weight
            key = (mask, 1 if signed_weight >= 0 else -1)
            prob = abs(signed_weight)
            mass[key] = mass.get(key, D(0)) + prob
            signed_cost[key] = signed_cost.get(key, D(0)) + ell * prob
            total_nonconstant += prob
            proxy_cost += ell * prob
    # Within a fixed parity mask, all index words have the same sign.
    # Hence aggregating powers above causes no cancellation at one order.
    assert abs(total_nonconstant - sum(abs(coeff[j]) * k**j
                                      for j in range(1, ORDER + 1))) < TOL
    assert total_nonconstant + abs(r) <= 1 + TOL
    for sign in (-1, 1):
        key = (0, sign)
        mass[key] = mass.get(key, D(0)) + (1 + sign*r - total_nonconstant) / 2
    assert min(mass.values()) >= -TOL
    assert abs(sum(mass.values()) - 1) < TOL

    support_cost = sum(D(mask.bit_count()) * prob
                       for (mask, _), prob in mass.items())
    assert support_cost <= D(1)/3 + TOL
    sk, ck = sincos(k)
    c_bound = k * (1-r*r) / (ck-abs(r)*sk)**2
    assert proxy_cost <= c_bound + TOL

    # A larger analytic radius gives certified bounds on the omitted
    # series terms, apart from the finite precision of this check.
    radius = D("0.3")
    sr, cr = sincos(radius)
    a_radius = (1-r*r) * sr / (cr-abs(r)*sr)
    c_radius = radius * (1-r*r) / (cr-abs(r)*sr)**2
    tail_mass = a_radius * (k/radius)**(ORDER+1)
    tail_cost = c_radius * (k/radius)**(ORDER+1)
    rho = D(2)/3 * D("0.4").exp()
    worst_posterior = D(0)
    worst_rejection = D(0)
    for spins in product((-1, 1), repeat=n):
        u = sum(a*x for a, x in zip(couplings, spins))
        truth = tanh(b+u)
        probs = {1: D(0), -1: D(0)}
        numer = {1: D(0), -1: D(0)}
        length_numer = {1: D(0), -1: D(0)}
        for (mask, sign), prob in mass.items():
            output = sign
            for j, spin in enumerate(spins):
                if mask & (1 << j):
                    output *= spin
            probs[output] += prob
            numer[output] += mask.bit_count() * prob
            length_numer[output] += signed_cost.get((mask, sign), D(0))
        assert abs(probs[1] - probs[-1] - truth) <= tail_mass + TOL
        for y in (-1, 1):
            p = (1 + y*truth)/2
            assert p > 0
            # Check the exact signed-numerator identity up to the tail.
            target = (proxy_cost + y*u*(1-truth*truth))/2
            assert abs(length_numer[y]-target) <= tail_cost/2 + TOL
            conditional = numer[y] / probs[y]
            rejection = support_cost / probs[y]
            assert conditional <= rho
            assert rejection < 2
            worst_posterior = max(worst_posterior, conditional)
            worst_rejection = max(worst_rejection, rejection)
    return worst_posterior, worst_rejection


def main():
    count = 0
    max_posterior = max_rejection = D(0)
    for n, k, field, shape in product(
        (1, 2, 4), (D("0.05"), D("0.125"), D("0.2")),
        (D(-40), D(-3), D("-0.7"), D(0), D("0.7"), D(3), D(40)),
        ("equal", "signed_skew"),
    ):
        weights = [D(1) if shape == "equal" else D(j+1) for j in range(n)]
        denom = sum(weights)
        couplings = [k*w/denom * (-1 if shape == "signed_skew" and j % 2 else 1)
                     for j, w in enumerate(weights)]
        posterior, rejection = check_map(couplings, field)
        max_posterior = max(max_posterior, posterior)
        max_rejection = max(max_rejection, rejection)
        count += 1

    p = Fraction(9, 265)
    flipped = Fraction(1, 65)
    lower = 2 * (1 - flipped/p)
    assert lower == Fraction(128, 117) > 1
    alpha = 2 * (Fraction(3, 2)-1)/(Fraction(3, 2)+1)
    assert alpha == Fraction(2, 5)
    print(f"PASS: {count} local-map cases, {ORDER} Taylor orders, 100-digit arithmetic")
    print(f"Largest tested posterior support: {float(max_posterior):.9f}")
    print(f"Largest tested rejection support cost: {float(max_rejection):.9f}")
    print(f"Exact obstruction: alpha={alpha}, posterior support >= {lower}")


if __name__ == "__main__":
    main()
