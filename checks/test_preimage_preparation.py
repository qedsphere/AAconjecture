"""Exact tiny-circuit checks; no code decoder or full YZ prover is simulated."""
from fractions import Fraction as F
from itertools import product
from math import prod

import pytest

from scripts.preimage_preparation import (
    all_boolean_tables, kickback_coefficients, prepared_coefficients, statistics,
)


@pytest.mark.parametrize("size", [1, 2, 4, 8])
def test_one_query_circuit_and_amplitudes(size):
    for table in all_boolean_tables(size):
        phase, unused = kickback_coefficients(table)
        assert all(value == 0 for value in unused)
        for z, bit in enumerate(table):
            assert phase[2*z] == (-1)**bit
            assert phase[2*z+1] == 1
        p = F(sum(table), size)
        coeff = prepared_coefficients(table)
        for z, bit in enumerate(table):
            assert coeff[2*z] == (3-2*p if bit else 1-2*p)
            assert coeff[2*z+1] == 1-2*p
        values = statistics(table)
        assert values["norm"] == 1
        assert values["joint_leakage"] == (1-p/2)*(1-2*p)**2
        assert values["herald_failure"] == (1-p)*(1-2*p)**2
        if p == F(1, 2):
            assert values["joint_leakage"] == values["herald_failure"] == 0
        # All good symbols have the same dummy-register vector: after a
        # positive H measurement, the symbol and dummy registers factor.
        good_vectors = {tuple(coeff[2*z:2*z+2]) for z, bit in enumerate(table) if bit}
        assert len(good_vectors) <= 1


@pytest.mark.parametrize("size", [1, 2, 4, 8])
def test_exact_uniform_oracle_averages(size):
    values = [statistics(table) for table in all_boolean_tables(size)]
    assert sum(v["joint_leakage"] for v in values)/len(values) == F(3, 4*size)
    assert sum(v["herald_failure"] for v in values)/len(values) == F(1, 2*size)
    assert sum((v["p"]-F(1, 2))**2 for v in values)/len(values) == F(1, 4*size)
    assert sum((v["p"]-F(1, 2))**3 for v in values) == 0


@pytest.mark.parametrize("size,coordinates", [(2, 2), (2, 3), (4, 2)])
def test_tensor_product_error_budget(size, coordinates):
    tables = list(all_boolean_tables(size))
    stats = {table: statistics(table) for table in tables}
    coefficients = {table: prepared_coefficients(table) for table in tables}
    average_joint_loss = F(0)
    average_herald_abort = F(0)
    for family in product(tables, repeat=coordinates):
        tensor = [prod(basis_coefficients) for basis_coefficients in
                  product(*(coefficients[table] for table in family))]
        assert sum(v*v for v in tensor)/(2*size)**coordinates == 1
        leakages = [stats[table]["joint_leakage"] for table in family]
        joint_loss = 1-prod(1-f for f in leakages)
        assert 0 <= joint_loss <= sum(leakages)
        herald_abort = 1-prod(stats[table]["herald_success"] for table in family)
        assert herald_abort <= sum(stats[table]["herald_failure"] for table in family)
        average_joint_loss += joint_loss
        average_herald_abort += herald_abort
    count = len(tables)**coordinates
    assert average_joint_loss/count == 1-(1-F(3, 4*size))**coordinates
    assert average_herald_abort/count == 1-(1-F(1, 2*size))**coordinates


def test_full_cell_query_can_ignore_other_answer_bits():
    # One arbitrary three-bit cell value. Other answer bits are |+>.
    bits = 3
    for cell_value, selected, a in product(range(1 << bits), range(bits), (0, 1)):
        initial = [(-1)**((1-a)*((answer >> selected) & 1))
                   for answer in range(1 << bits)]
        after_xor = [initial[answer ^ cell_value] for answer in range(1 << bits)]
        after_unphase = [value * (-1)**((1-a)*((answer >> selected) & 1))
                         for answer, value in enumerate(after_xor)]
        # All answer Hadamards undo the preparation; only output 000 remains.
        final = [sum(value * (-1)**((answer & out).bit_count())
                     for answer, value in enumerate(after_unphase))/F(1 << bits)
                 for out in range(1 << bits)]
        assert final[0] == (-1)**((1-a)*((cell_value >> selected) & 1))
        assert all(value == 0 for value in final[1:])


def test_unbalanced_oracles_are_not_claimed_to_prepare_the_joint_target_exactly():
    empty = statistics((0, 0, 0, 0))
    sparse = statistics((1, 0, 0, 0))
    full = statistics((1, 1, 1, 1))
    assert empty["joint_leakage"] == empty["herald_failure"] == 1
    assert sparse["joint_leakage"] == F(7, 32) > 0
    assert full["joint_leakage"] == F(1, 2)
    assert full["herald_failure"] == 0


def test_plain_grover_at_half_density_does_not_fix_rejection():
    p = F(1, 2)
    assert p*(3-4*p)**2 == F(1, 2)
    diluted = p/2
    assert diluted*(3-4*diluted)**2 == 1
