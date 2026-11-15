"""Exact finite parameter tests; the report supplies the asymptotic proof."""
from fractions import Fraction as F

import pytest

from scripts.yz_list_recovery import check_parameters, parameters


@pytest.mark.parametrize("b", [22, 23, 24, 25, 26])
def test_both_source_inequalities_and_verification_slack(b):
    result = check_parameters(b)
    assert result["source_eq8"]
    assert result["source_eq9"]
    assert result["final_verification_fits"]
    assert result["usable_soundness"]


@pytest.mark.parametrize("rate", [F(9, 10), F(15, 16)])
def test_additional_fixed_rates(rate):
    result = check_parameters(26, rate)
    assert result["usable_soundness"]


@pytest.mark.parametrize("b", [20, 21])
def test_small_parameters_do_not_justify_appending_verification(b):
    # Negative examples: source inequalities pass, but T+n<=ell fails.
    # This is why the theorem states "sufficiently large lambda".
    result = check_parameters(b)
    assert result["source_eq8"] and result["source_eq9"]
    assert not result["final_verification_fits"]
    assert not result["usable_soundness"]


def test_limit_slack_and_integer_rounding_bounds():
    for rate in (F(7, 8), F(9, 10), F(15, 16)):
        zeta = (1-rate)/4
        # The written proof uses 2^zeta <= 1+zeta for 0<=zeta<=1.
        # Check the remaining algebra, not a floating-point exponential.
        assert rate*(1+zeta) == 1-3*zeta-4*zeta*zeta < 1-zeta
        for b in (22, 24, 26):
            p = parameters(b, rate)
            assert p["nc"] == p["n"]*p["m"] == p["q"]-1
            assert p["r"] == p["m"] and 1 <= p["s"] <= p["m"]
            lead = zeta*zeta*p["n"]/(4*p["log_q"])
            assert lead-zeta-1 < p["log_ell"] <= lead
            assert p["log_list"] <= zeta*p["n"]/4


def test_power_guard_prevents_unbounded_local_computation():
    with pytest.raises(ValueError, match="Exact-power guard"):
        check_parameters(28)


def test_no_root_or_inequality_direction_error_in_small_auxiliary_example():
    # Compare the cleared-integer formula against the original positive
    # rational expressions raised to s+1. This is NOT a new code theorem.
    q, m, s, rate, zeta, ell = 16, 5, 2, F(7, 8), F(1, 32), 2
    nc = q-1
    kappa = int(rate*nc)
    r = m
    source_lhs = (1-zeta)*nc/m
    source_rhs_prefactor = (1+F(s, r))/(m-s+1)
    original8 = source_lhs**(s+1) >= source_rhs_prefactor**(s+1)*nc*ell*kappa**s
    normalized = (1-zeta)*(m-s+1)/(m+s)
    cleared8 = normalized.numerator**(s+1)*nc**s >= normalized.denominator**(s+1)*ell*kappa**s
    assert original8 == cleared8
    original9 = F(nc*ell, kappa) < F(q, r+s)**(s+1)
    cleared9 = (r+s)**(s+1)*nc*ell < q**(s+1)*kappa
    assert original9 == cleared9
