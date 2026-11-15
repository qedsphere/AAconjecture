# Unified AA: Lean 4 formalization

This is an **initial formalization checkpoint**, not a formalization of the
whole paper. The probability core of heavy-output extraction is proved with
exact real arithmetic and arbitrary finite types. No theorem uses `sorry`,
`admit`, a project axiom, or native evaluation as a proof.

## Build

Run in this directory:

```sh
lake update
lake exe cache get
lake build
sh scripts/check.sh
```

Lean is pinned to **4.33.0**. `lake-manifest.json` pins dependencies, including
[the supplied AA formalization](https://github.com/physical-superintelligence/aaronson-ambainis/tree/2a6ceaef872ae993708950f951989134084b851a).
The check script uses `uv run --no-project` for a standard-library-only axiom
report checker. It needs no additional Python packages.

## Proved extraction components

| Paper location | Lean declaration | Scope |
|---|---|---|
| §4.3, p. 26 | `bucketMass_eq` | Heavy atom plus contaminating mass equals bucket mass |
| Theorem 4.1 proof | `decodeBit_correct`, `decodeString_correct` | Exact threshold reconstruction with isolation ≤t/4 and additive errors ≤t/16 |
| Corollary 4.2 proof | `exists_heavy_of_sparse_mass` | A set of ≤k outputs carrying mass ≥alpha contains an alpha/k-heavy atom |
| Theorem 4.1 proof | `expected_contamination_le` | Pair-collision bound implies expectation bound |
| Theorem 4.1 proof | `isolation_failure_le_quarter` | Isolation fails with probability ≤1/4 whenever B*t≥16 |
| Theorem 4.1 proof | `simultaneous_estimate_failure_le` | Union bound over exactly B(L+1) scalar estimates |
| Theorem 4.1 proof | `FiniteLaw.extraction_event_bound` | Independent table/hash sampling, aggregate estimation failure, and rho/2 success |
| Theorem 4.1 probability conclusion | `heavy_output_list_success` | Actual decoded list contains a valid output with probability ≥rho/2 |

`heavy_output_list_success` assumes a pair-collision bound and a simultaneous
estimator failure bound. It proves a list-success probability, **not the
existence or query cost of a classical oracle algorithm**. The estimator
functions in this theorem are arbitrary functions satisfying the error
hypothesis; they are not secretly assumed to be query bounded. The finite
probability model uses normalized nonnegative weights and product weights
for independent sampling. No independence between isolation and accuracy
events is assumed. A heavy witness may depend on the table but never on
the independently sampled hash.

The core build and axiom audit succeeded on 2026-11-15 with Lean 4.33.0:
13 key theorem reports (11 extraction results and two AA statement adapters)
depend only on `propext`, `Classical.choice`, and `Quot.sound`. Logs are under
`artifacts/`. These are kernel-checked universal
theorems, not finite experiments. This audit does not independently replay
the Mathlib kernel environment or prove correspondence to informal prose.

## Decision-tree checkpoint

`DecisionTree.lean` now defines deterministic Boolean-oracle evaluation,
physical query counts, worst-case depth, and truncation at a stored summary.
Its finite-tree potential argument proves `gamma * expectedQueries ≤ potential`
under an explicit drift hypothesis. `Uniform.lean` supplies uniform finite
laws and a coordinate-flip averaging identity. `DecisionTreeUniform.lean`
proves that fresh-coordinate trees have exactly their fair-branch expected
cost under a uniformly random Boolean table. Consequently truncating after
K>0 queries changes the original tree's answer on probability at most
`potential(root)/(gamma*K)`, with a deterministic worst-case cap of K.

The stored summaries have not yet been proved to be conditional means of
the target polynomial. The drift hypothesis has not yet been constructed
from polynomial restrictions and AA. This checkpoint establishes the tree
and truncation machinery, not the completed scalar estimator.

The four-person ownership and integration plan is in
[`PARALLELISATION.md`](../PARALLELISATION.md).

## AA interface

`UnifiedAA/Influence.lean` defines Boolean cube evaluation, mean, variance,
and flip influence in the upstream normalization. It adapts
`AaronsonAmbainis.PrintedConjecture` and derives the coarser
epsilon^8/d^12 influence scale used in the manuscript, for epsilon≤1 and
d≥1. Its explicit `hAA` argument is meant to be instantiated with the
upstream proved `AaronsonAmbainis.aaronson_ambainis`; it is not a new axiom
or a claim that AA is unresolved.

The interface compiled successfully too, and is included in the default
library build. To build just that module:

```sh
lake build UnifiedAA.Influence
```

The full upstream `Main` rebuild was attempted locally and stopped at this
bounded checkpoint. Its large parallel imports strained the 16 GiB local
machine. The imported statement module compiled; a complete local recheck
of the upstream proof is not claimed. The extraction core does not use AA
until the scalar estimator construction has been formalized.

## Remaining work

The next substantive dependency is §2.4's **scalar simulation construction**:
restriction invariants, the polynomial influence-potential drop, construction
of a fresh tree satisfying the proved drift theorem, and conditional Chebyshev
error. A quantum query model and degree bound,
affine hashing, verifier composition and query accounting then complete
Theorem 4.1. Tablewise amplification completes Corollary 4.2.

The Gibbs theorem, entropy/extraction conclusions, YZ refinements, honest
preparation, and sparse sampling remain unformalized. See `TODO.md` for the
dependency order and `RESEARCH.md` for exact first-checkpoint hypotheses.

The manuscript snapshots are under `sources/`. The supplied TeX wrapper
references nine unavailable section files. Statements were recovered from
the matching PDF; page 26 was visually checked. The section sources were
requested so future mappings can use stable theorem labels.
