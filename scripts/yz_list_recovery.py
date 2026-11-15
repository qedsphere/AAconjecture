"""Bounded exact checks of the YZ Lemma 4.3 parameter retuning.

Only integer powers and rational arithmetic are used. The code verifies the
two inequalities for supplied finite parameters; it does not prove the
coding theorem, its asymptotics, classical hardness, or the AA theorem.

Example: uv run --no-sync scripts/yz_list_recovery.py --b 20 21 22 23 24 25 26
"""
import argparse
from fractions import Fraction as F
import json


def floor_fraction(value):
    return value.numerator // value.denominator


def parameters(b, rate=F(7, 8)):
    rate = F(rate)
    if not 2 <= b <= 64 or not F(5, 6) < rate < 1:
        raise ValueError("Require 2<=b<=64 and fixed 5/6<rate<1")
    q = 1 << (2*b)
    m, n = (1 << b) + 1, (1 << b) - 1
    nc = q - 1
    kappa = floor_fraction(rate * nc)
    zeta = (1-rate)/4
    s = floor_fraction(zeta*n/(4*(2*b)))
    log_ell = floor_fraction(zeta*s)
    return dict(b=b, rate=rate, q=q, m=m, n=n, nc=nc, kappa=kappa,
                zeta=zeta, s=s, r=m, log_q=2*b, log_ell=log_ell,
                log_list=s*(2*b), unseen=floor_fraction(zeta*n))


def check_parameters(b, rate=F(7, 8), max_s=20_000):
    p = parameters(b, rate)
    s, m, q, nc, kappa = (p[key] for key in ("s", "m", "q", "nc", "kappa"))
    if s > max_s:
        raise ValueError(f"Exact-power guard: s={s} exceeds max_s={max_s}")
    if s < 1 or s > m:
        raise ValueError("Source lemma requires 1<=s<=m")
    ell = 1 << p["log_ell"]
    agreement = 1-p["zeta"]
    # For r=m, normalized Eq. (8) is
    # [(1-zeta)(m-s+1)/(m+s)]^{s+1} >= ell*(kappa/nc)^s.
    # Clear positive denominators, preserving the inequality exactly.
    lhs8 = (agreement.numerator*(m-s+1))**(s+1) * nc**s
    rhs8 = (agreement.denominator*(m+s))**(s+1) * ell * kappa**s
    eq8 = lhs8 >= rhs8
    # Eq. (9), raised to s+1: (r+s)^{s+1} nc ell < q^{s+1} kappa.
    eq9 = (m+s)**(s+1) * nc * ell < q**(s+1) * kappa
    log_soundness = p["log_list"] - p["unseen"]
    ceiling_log = p["log_ell"]-1
    verification_budget = ceiling_log >= 0 and (1 << ceiling_log) + p["n"] <= ell
    assert F(p["log_list"]) <= p["zeta"]*p["n"]/4
    assert F(log_soundness) <= 1 - 3*p["zeta"]*p["n"]/4
    return dict(b=b, rate=str(p["rate"]), n=p["n"], s=s,
                log2_ell=p["log_ell"], log2_T=ceiling_log,
                log2_list_bound=p["log_list"], unseen_bits=p["unseen"],
                log2_soundness_bound=log_soundness,
                source_eq8=eq8, source_eq9=eq9,
                final_verification_fits=verification_budget,
                usable_soundness=eq8 and eq9 and verification_budget and log_soundness < 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--b", nargs="+", type=int, default=list(range(20, 27)))
    parser.add_argument("--rate", type=F, default=F(7, 8))
    args = parser.parse_args()
    results = [check_parameters(b, args.rate) for b in args.b]
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
