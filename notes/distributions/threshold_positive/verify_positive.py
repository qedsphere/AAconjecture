"""Finite checks for the block rounding and Ising-forest posterior proofs.

Run from any directory; the JSON report is written beside this script.
These checks supplement the mathematical proof, not formal verification.
"""

import itertools
import json
import math
from pathlib import Path


SPINS = (-1, 1)


def forest_check(parents, beta, couplings, fields):
    n = len(parents)
    roots = [i for i, p in enumerate(parents) if p < 0]
    edges = [(p, v) for v, p in enumerate(parents) if p >= 0]
    xs = list(itertools.product(SPINS, repeat=n))
    weights = {
        x: math.exp(beta * (
            sum(couplings[v] * x[u] * x[v] for u, v in edges)
            + sum(h * spin for h, spin in zip(fields, x))
        )) for x in xs
    }
    z = sum(weights.values())
    mu = {x: p / z for x, p in weights.items()}
    roots_law = {
        r: {s: sum(p for x, p in mu.items() if x[r] == s) for s in SPINS}
        for r in roots
    }
    kernels = {}
    reset = {}
    continuation = {}
    signs = {}
    max_posterior_copy = 0.0
    for u, v in edges:
        kernels[v] = {
            s: {
                t: sum(p for x, p in mu.items() if x[u] == s and x[v] == t)
                / sum(p for x, p in mu.items() if x[u] == s)
                for t in SPINS
            } for s in SPINS
        }
        m = {t: min(kernels[v][s][t] for s in SPINS) for t in SPINS}
        q = sum(m.values())
        lam = max(0.0, 1.0 - q)
        continuation[v] = lam
        reset[v] = {t: m[t] / q for t in SPINS}
        signs[v] = 1 if couplings[v] >= 0 else -1
        for s in SPINS:
            for t in SPINS:
                expected = q * reset[v][t] + lam * (t == signs[v] * s)
                assert abs(expected - kernels[v][s][t]) < 2e-13
                if t == signs[v] * s:
                    max_posterior_copy = max(max_posterior_copy, lam / kernels[v][s][t])

    reconstructed = {}
    for x in xs:
        value = math.prod(roots_law[r][x[r]] for r in roots)
        value *= math.prod(kernels[v][x[u]][x[v]] for u, v in edges)
        reconstructed[x] = value
    kernel_error = max(abs(mu[x] - reconstructed[x]) for x in xs)
    assert kernel_error < 1e-12

    # Enumerate independent root and edge source bits.
    source_marginal = {x: 0.0 for x in xs}
    bad = {ell: {x: [0.0] * n for x in xs} for ell in (1, 2)}
    posterior_product_error = 0.0
    for root_values in itertools.product(SPINS, repeat=len(roots)):
        root_source = dict(zip(roots, root_values))
        root_probability = math.prod(roots_law[r][root_source[r]] for r in roots)
        for edge_values in itertools.product(itertools.product((0, 1), SPINS), repeat=len(edges)):
            edge_source = {v: source for (_, v), source in zip(edges, edge_values)}
            probability = root_probability
            x_list = [0] * n
            for v in range(n):
                if parents[v] < 0:
                    x_list[v] = root_source[v]
                else:
                    c, y = edge_source[v]
                    lam = continuation[v]
                    probability *= (lam if c else 1 - lam) * reset[v][y]
                    x_list[v] = signs[v] * x_list[parents[v]] if c else y
            x = tuple(x_list)
            source_marginal[x] += probability
            posterior_product = 1.0
            for u, v in edges:
                c, y = edge_source[v]
                lam = continuation[v]
                term = (lam if c else 1 - lam) * reset[v][y]
                term /= kernels[v][x[u]][x[v]]
                posterior_product *= term
            posterior_product_error = max(
                posterior_product_error,
                abs(probability / mu[x] - posterior_product),
            )
            for ell in (1, 2):
                for start in range(n):
                    v = start
                    sign = 1
                    value = None
                    for _ in range(ell):
                        if parents[v] < 0:
                            value = sign * root_source[v]
                            break
                        c, y = edge_source[v]
                        if not c:
                            value = sign * y
                            break
                        sign *= signs[v]
                        v = parents[v]
                    if value is None and parents[v] < 0:
                        value = sign * root_source[v]
                    if value is None:
                        value = 1
                    if value != x[start]:
                        bad[ell][x][start] += probability

    source_error = max(abs(source_marginal[x] - mu[x]) for x in xs)
    assert source_error < 1e-12
    assert posterior_product_error < 2e-12
    jstar = max((abs(couplings[v]) for _, v in edges), default=0.0)
    rho = 1 - math.exp(-4 * beta * jstar)
    assert max_posterior_copy <= rho + 2e-12
    truncation = {}
    for ell in (1, 2):
        mismatch = max(value / mu[x] for x, values in bad[ell].items() for value in values)
        assert mismatch <= rho ** ell + 2e-12
        truncation[ell] = {"maximum_conditional_mismatch": mismatch, "bound": rho ** ell}
    return {
        "parents": parents,
        "beta": beta,
        "maximum_kernel_reconstruction_error": kernel_error,
        "maximum_source_marginal_error": source_error,
        "maximum_posterior_factorization_error": posterior_product_error,
        "maximum_posterior_copy": max_posterior_copy,
        "posterior_copy_bound": rho,
        "truncation": truncation,
    }


def block_rounding_check():
    cases = []
    for k in (1, 2, 3):
        length = 2 ** k
        for eta in (0.05, 0.25):
            for mode in ("point_mass", "uniform", "rare_atoms"):
                if mode == "point_mass":
                    p = [1.0] + [0.0] * (length - 1)
                elif mode == "uniform":
                    p = [1.0 / length] * length
                else:
                    raw = [10.0 ** (-5 * i) for i in range(length)]
                    p = [v / sum(raw) for v in raw]
                b = k + math.ceil(math.log2(1.0 / eta))
                n = 2 ** b
                counts = [math.ceil((1 - eta) * n * v) for v in p]
                assert sum(counts) <= n
                counts[0] += n - sum(counts)
                residual = [(c / n - (1 - eta) * v) / eta for c, v in zip(counts, p)]
                assert min(residual) >= -1e-14
                assert abs(sum(residual) - 1) < 1e-13
                cases.append({"block_size": k, "eta": eta, "mode": mode, "source_bits": b})
    return cases


def main():
    tree_cases = []
    shapes = [[-1, 0, 1, 2, 3], [-1, 0, 0, 0, 0], [-1, 0, 0, 1, 1], [-1, -1, 0, 1, 2]]
    parameters = [
        (0.0, [0.0, 1.0, 1.0, 1.0, 1.0], [0.0] * 5),
        (0.7, [0.0, 0.5, -0.9, 0.0, 1.2], [0.0, -1.3, 2.1, -0.6, 0.2]),
        (1.1, [0.0, -0.8, 1.2, -1.0, 0.4], [-1.0, 0.2, 0.4, 1.7, -2.3]),
    ]
    for parents in shapes:
        for beta, couplings, fields in parameters:
            tree_cases.append(forest_check(parents, beta, couplings, fields))
    report = {
        "status": "all assertions passed",
        "scope": "finite enumeration supplements analytical proofs; not formal verification",
        "block_rounding_cases": block_rounding_check(),
        "forest_cases": tree_cases,
    }
    output = Path(__file__).with_name("verification.json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {len(report['block_rounding_cases'])} block-rounding cases and {len(tree_cases)} forest cases.")
    print(f"Wrote {output}")


if __name__ == "__main__":
    main()
