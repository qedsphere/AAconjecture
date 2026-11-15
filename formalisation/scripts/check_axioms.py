"""Validate Lean's dependency report, not just source spelling of placeholders."""
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "UnifiedAA.bucketMass_eq",
    "UnifiedAA.decodeBit_correct",
    "UnifiedAA.decodeString_correct",
    "UnifiedAA.exists_heavy_of_sparse_mass",
    "UnifiedAA.FiniteLaw.prob_exists_le_sum",
    "UnifiedAA.FiniteLaw.prob_not_forall_le",
    "UnifiedAA.expected_contamination_le",
    "UnifiedAA.isolation_failure_le_quarter",
    "UnifiedAA.simultaneous_estimate_failure_le",
    "UnifiedAA.FiniteLaw.extraction_event_bound",
    "UnifiedAA.heavy_output_list_success",
    "UnifiedAA.polynomial_has_influential_coordinate",
    "UnifiedAA.coarse_influence_bound",
    "UnifiedAA.uniform_expect_branch",
    "UnifiedAA.DecisionTree.queries_le_depth",
    "UnifiedAA.DecisionTree.depth_truncate_le",
    "UnifiedAA.DecisionTree.queries_truncate_le",
    "UnifiedAA.DecisionTree.eval_truncate_eq_of_queries_le",
    "UnifiedAA.DecisionTree.expectedQueries_mul_le_potential",
    "UnifiedAA.DecisionTree.truncation_failure_bound",
    "UnifiedAA.DecisionTree.uniform_expected_queries",
    "UnifiedAA.DecisionTree.uniform_truncation_failure_bound",
}

text = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
reports += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
found = set()
for theorem, axiom_list in reports:
    axioms = {a.strip() for a in axiom_list.split(",") if a.strip()}
    extra = axioms - ALLOWED
    if extra:
        raise SystemExit(f"FAIL: {theorem} uses {sorted(extra)}")
    found.add(theorem)
if found != EXPECTED:
    raise SystemExit(f"FAIL: missing={EXPECTED - found}; unexpected={found - EXPECTED}")
if re.search(r"\berror:|\bsorryAx\b", text):
    raise SystemExit("FAIL: error or placeholder axiom in Lean report")
print(f"PASS: {len(found)} theorems; only {', '.join(sorted(ALLOWED))}")
