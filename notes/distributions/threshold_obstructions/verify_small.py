"""Finite enumeration checks for the soft-code proof (not an asymptotic proof)."""
import itertools
import json
from pathlib import Path
import numpy as np


def logsumexp(a, axis):
    maximum = np.max(a, axis=axis, keepdims=True)
    return np.squeeze(maximum, axis=axis) + np.log(np.sum(np.exp(a - maximum), axis=axis))


def normalized(log_weights):
    return np.exp(log_weights - logsumexp(log_weights, axis=0))


def check(m, strength):
    n = 2 ** m
    indices = np.arange(n)
    characters = np.array([[(-1) ** ((int(a) & int(z)).bit_count() % 2)
                            for z in indices] for a in indices], dtype=float)
    signed = np.concatenate([characters, -characters])
    configs = 1.0 - 2.0 * ((np.arange(2 ** n)[:, None] >> indices[None, :]) & 1)
    scores = configs @ signed.T
    labels = np.array([sum(((a >> j) & 1) * ((a >> (j + 1)) & 1)
                           for j in range(0, m, 2)) % 2 for a in indices])
    r = float(np.mean(labels))
    p = np.sum((configs @ characters[labels == 1].T / n) ** 2, axis=1)
    log_s = logsumexp(strength * scores, axis=1)
    result = {"m": m, "n": n, "L": strength, "temperatures": []}
    assert np.min(p) > -1e-12 and np.max(p) < 1 + 1e-12
    hamiltonian = -log_s
    flip_max = max(float(np.max(np.abs(hamiltonian - hamiltonian[
        np.arange(2 ** n) ^ (1 << j)]))) for j in indices)
    result["max_single_flip_energy"] = flip_max
    result["energy_range"] = float(np.ptp(hamiltonian))
    assert flip_max <= 2 * strength + 1e-12
    assert np.ptp(hamiltonian) <= np.log(np.cosh(strength * n)) + 1e-12
    for beta in (0.3, 1.0, 2.0):
        rho = np.tanh(beta * strength)
        q = normalized(logsumexp(beta * strength * scores, axis=1))
        mu = normalized(beta * log_s)
        eq = float(q @ p)
        varq = float(q @ ((p - eq) ** 2))
        target_var = r * (1 - r) * (rho ** 4 + 2 * (1 - rho ** 4) / n)
        assert abs(eq - r) < 1e-11 and abs(varq - target_var) < 1e-11
        conditional_error = 0.0
        for a in indices:
            component = normalized(beta * strength * scores[:, a])
            target = (1 - rho ** 2) * r + rho ** 2 * labels[a]
            conditional_error = max(conditional_error, abs(float(component @ p) - target))
        assert conditional_error < 1e-11
        marginal_error = 0.0
        for degree in (1, 2, 3):
            for subset in itertools.combinations(range(n), degree):
                marginal_error = max(marginal_error, abs(float(mu @ np.prod(configs[:, subset], axis=1))))
        assert marginal_error < 1e-11
        log_r = beta * log_s - logsumexp(beta * strength * scores, axis=1)
        assert np.min(log_r) >= min(beta - 1, 0) * np.log(2 * n) - 1e-11
        assert np.max(log_r) <= max(beta - 1, 0) * np.log(2 * n) + 1e-11
        tv = float(np.sum(np.abs(mu - q)) / 2)
        if beta == 1:
            assert tv < 1e-12
        result["temperatures"].append({"beta": beta, "rho_beta": float(rho),
            "comparison_tv": tv, "noisy_acceptance_mean": eq,
            "noisy_acceptance_variance": varq,
            "variance_formula_error": abs(varq - target_var),
            "max_conditional_mean_error": conditional_error,
            "max_moment_degree_le_3": marginal_error})
    return result


if __name__ == "__main__":
    results = {"checks": [check(2, 0.4), check(4, 0.4)], "status": "passed"}
    Path(__file__).with_name("verification.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
