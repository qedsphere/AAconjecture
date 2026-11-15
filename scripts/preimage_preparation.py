"""Exact finite state-vector model for diluted one-step Grover preparation.

The truth table is explicit. This Python simulation is NOT a classical
one-query algorithm; the modeled quantum circuit has one XOR-oracle gate.
All amplitudes are represented as rational coefficients times the common
normalization 1/sqrt(2S). Squared overlaps need no numerical square roots.
"""
from fractions import Fraction as F


def all_boolean_tables(size):
    for mask in range(1 << size):
        yield tuple((mask >> z) & 1 for z in range(size))


def kickback_coefficients(table):
    """Model prepare answer |-> or |+>, one XOR permutation, then unprepare."""
    if not table or len(table) & (len(table)-1) or any(bit not in (0, 1) for bit in table):
        raise ValueError("Require a nonempty power-of-two Boolean truth table")
    zero_answer, one_answer = [], []
    for fz in table:
        for a in (0, 1):
            # Before the oracle, target coefficients have common factor 1/sqrt(2).
            prepared = (1, -1 if a == 0 else 1)
            after_xor = [prepared[b ^ fz] for b in (0, 1)]
            # Undo the a-controlled Z, then the target Hadamard. The second
            # 1/sqrt(2) cancels the first relative to the main-state convention.
            if a == 0:
                after_xor[1] *= -1
            zero_answer.append(F(after_xor[0] + after_xor[1], 2))
            one_answer.append(F(after_xor[0] - after_xor[1], 2))
    return tuple(zero_answer), tuple(one_answer)


def prepared_coefficients(table):
    phase, unused = kickback_coefficients(table)
    if any(unused):
        raise AssertionError("Answer register did not uncompute")
    mean = sum(phase, F(0))/len(phase)
    return tuple(2*mean-value for value in phase)


def statistics(table):
    coeff = prepared_coefficients(table)
    size = len(table)
    norm = sum(value*value for value in coeff)/(2*size)
    marked_overlap_squared = sum((coeff[2*z]**2 for z, bit in enumerate(table) if bit),
                                 F(0))/(2*size)
    herald_success = sum((coeff[2*z+a]**2 for z, bit in enumerate(table) if bit
                          for a in (0, 1)), F(0))/(2*size)
    return dict(p=F(sum(table), size), norm=norm,
                marked_overlap_squared=marked_overlap_squared,
                joint_leakage=1-marked_overlap_squared,
                herald_success=herald_success, herald_failure=1-herald_success)
