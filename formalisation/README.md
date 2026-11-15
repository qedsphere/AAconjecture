# Unified AA: Lean 4 formalization

This is a **partial formalization**, not a formalization of the
whole paper. The probability core of heavy-output extraction is proved with
exact real arithmetic and arbitrary finite types. No theorem uses `sorry`,
`admit`, a project axiom, or native evaluation as a proof.

## Build

Run in this directory. On a space-constrained machine, use the recorded
import-only patch after dependencies have been fetched; it preserves all
upstream AA statements while avoiding the aggregate `Mathlib` import:

```sh
git -C .lake/packages/AaronsonAmbainis apply --unidiff-zero ../../../patches/aa-conjecture-imports.patch
python3 scripts/build_serial.py --cache UnifiedAA
sh scripts/check.sh
```

Apply the patch only once per dependency checkout. It affects only
`AaronsonAmbainis/Conjecture.lean`'s imports, not the upstream proof or any
statement. The serial build script downloads the directly imported Mathlib
modules and their dependencies, then builds project and vendored modules in
dependency order. The check script also builds sequentially; avoid starting
concurrent Lean checks.
The separate full-proof check also needs the import-only proof patch:

```sh
git -C .lake/packages/AaronsonAmbainis apply --unidiff-zero ../../../patches/aa-proof-imports.patch
sh scripts/check.sh --proved-aa
```

Apply each patch only once. `--proved-aa` checks `UnifiedAA.ProvedAA`, including
the upstream `Main` closure and the nine corollaries with no explicit AA
hypothesis. This full-proof run was stopped at the user's publication checkpoint after
10 of 74 upstream modules passed. Resume at `AaronsonAmbainis.DetBij.Basic`.
`ProvedAA.lean` and its nine corollaries have not yet been compiled or audited. The default check covers the core aggregate.
For bounded upstream batches, `scripts/build_aa_serial.py --max-modules 3`
prints the next module explicitly. Resume with `--start-at MODULE
--max-modules 3`; Lake still checks each target's cached dependencies. A batch
completion is not a completed check of `Main`.
`python3 scripts/build_serial.py` without targets checks every local and
vendored module, including work outside the certified-randomness aggregate.

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

The certified-randomness aggregate build and expanded axiom audit succeeded
on 2026-11-15 with Lean 4.33.0: all 151 selected declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. This supersedes the original
13-result and later 101-result audit for the covered core. The additional 50
reports include affine bucket rounding, native/XOR operational extraction,
tablewise and sparse amplification, accepted-law entropy, and the generic
soundness contradiction. Logs are `artifacts/integration-core-check.log` and
`artifacts/axioms.log`. The audit checker's placeholder, extra-axiom, and missing
report rejection fixtures also passed (`artifacts/integration-audit-checker.log`).
These are kernel-checked universal
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

`ConditionalMeans.lean` now constructs exact mean summaries.
`InfluenceTree.lean` constructs a fresh tree from a restriction-stable
influence rule and proves the cost bound directly by induction on unread
coordinates. This avoids assigning a function-dependent potential to an
unannotated tree shape.

`CubeConditioning.lean` proves exact one-bit conditional-mean and squared-error
splits. `InfluencePotential.lean` proves nonnegativity and the exact potential
drop `Phi(f) - (Phi(f|i=0)+Phi(f|i=1))/2 = Inf_i(f)` for arbitrary real functions
on finite Boolean cubes. `ProbabilityBounds.lean` proves variance decomposition,
finite-law Chebyshev, and a joint-to-tablewise exceptional-set bound. These
modules compiled under Lean 4.33.0, and their eight headline results were
checked with `checks/NewAxioms.lean`; only standard Lean axioms appeared. The
degree bound `Phi(p) ≤ d` and the normalization adapter are now proved in
`PolynomialPotential.lean` and `CubeNormalization.lean`. The scalar construction
is completed conditional on the imported AA statement, as described below.

The four-person ownership and integration plan is in
[`PARALLELISATION.md`](../PARALLELISATION.md).

## AA interface

`UnifiedAA/CubeNormalization.lean` defines Boolean cube evaluation, mean,
variance, and flip influence in the upstream normalization. `Influence.lean` adapts
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
of the upstream proof is not claimed. The scalar simulator and quantum
extractor retain the explicit `hAA` parameter; finite probability and
reconstruction lemmas are independent of AA.

## Remaining work

The core still takes the imported AA statement as an explicit proof parameter.
`ProvedAA.lean` is prepared to discharge it using the pinned upstream
proved theorem, but is not yet checked. Affine hashes, power-of-two bucket rounding, native and XOR
extractors, verifier composition, tablewise amplification, and the sparse
search corollary are now in the checked core aggregate.

The generic accepted-output min-entropy theorem is also checked, conditional
on an actual bounded-query classical search-soundness hypothesis and its budget
inequality. Instantiating that hypothesis with the concrete YZ coding bounds,
seeded leftover hashing and global acceptance reweighting remain open.
The full Gibbs simulation, YZ refinements, honest preparation, and sparse
sampling are not completed by this checkpoint. See `TODO.md` for the remaining
dependencies.

The manuscript snapshots are under `sources/`. The supplied TeX wrapper
references nine unavailable section files. Statements were recovered from
the matching PDF; page 26 was visually checked. The section sources were
requested so future mappings can use stable theorem labels.

## Recursive scalar-error checkpoint

`ScalarError.lean` proves recursive leaf-variance aggregation, scalar error,
and its combination with deterministic K-query truncation. `ConditionalMeans.lean`
constructs exact conditional-mean summaries on any supplied tree shape and
preserves freshness and physical query counts. `variance_le_quarter` proves
the [0,1] variance bound for arbitrary finite laws. These results still require
a tree shape with small terminal variances. That shape, polynomial degree
preservation and the potential bound are now supplied by the modules below.

Targeted verification is available through `lake build UnifiedAA.ConditionalMeans`
and `checks/NewAxioms.lean`; these results are also included in the successful
151-result core aggregate audit.

`PolynomialRestrictions.lean` defines substitution of one Boolean variable by
a constant, proves that substitution cannot increase multivariate total degree,
and proves exact pointwise correspondence with `restrictBit`. Its proof uses
the targeted precompiled caches for `MvPolynomial.Monad` and
`MvPolynomial.NoZeroDivisors`, with one Lean build process at a time.

`UniformHashing.lean` proves the one-bit uniform-function collision probability.
`IndependentSampling.lean` constructs independent finite products and proves
the exact repetition-failure formula. `AffineHashing.lean` constructs the
compact affine parity family (one row and offset bit per output bit) and
proves exact collision probability `1/2^k` for distinct inputs. Bucket-count
rounding and composition with the operational extractor are proved in
`DyadicRounding.lean`, `AffineExtraction.lean`, and `XorExtraction.lean`.

## Polynomial scalar simulation checkpoint

`FourierPotential.lean` proves Walsh orthogonality, Parseval, the exact spectral
formula for squared-flip influence, and `Phi(f) ≤ 4d E[f²]`.
`PolynomialPotential.lean` bridges total polynomial degree to Walsh degree and
centers bounded functions at `1/2` to prove `Phi(p) ≤ d`.
`CubeNormalization.lean` identifies the generic finite-law means, variances and
influences with the original `Fin N` AA interface; the definitions moved from
`Influence.lean` without changing their values or names.

`InfluenceTree.lean` and `PolynomialSimulation.lean` construct fresh, terminating
conditional-mean trees from an influence rule, prove expected query cost, and
bound truncation error. `ScalarSimulation.lean` obtains that rule from
`hAA : AaronsonAmbainis.PrintedConjecture`. For `d ≥ 1` and `0 < e,delta ≤ 1`,
`exists_aa_scalar_estimator_explicit` gives an actual deterministic tree with
at most `ceil(512*d^13/(e^16*delta^9))` queries and uniform-table error probability
at most `delta`. This remains conditional on `hAA` until the upstream `Main`
proof is imported and checked locally.

## Quantum bridge

`QuantumSimulation.lean` connects the polynomial estimator to actual quantum
query algorithms. It proves the degree-2q acceptance-polynomial and [0,1]
range interfaces for both native value queries and padded Boolean XOR queries.
Both yield a deterministic scalar tree with budget
`ceil(512*(2*q+1)^13/(e^16*delta^9))`, conditional on `hAA`. Fixed output
postprocessing also supplies bucket and bit masses, and a finite family of
predicates admits estimators chosen before sampling the table.

The bridge reuses twelve source modules from
[Troy Lee's quantum-query-complexity library](https://github.com/troyjlee/quantum-query-complexity/tree/df7f2e8199bd845a35a4200e0c74d964ec6b02b8),
vendored with its Apache-2.0 license and provenance in
`vendor/quantum-query-complexity/README.md`. All twelve modules compiled
unchanged under this project's Lean 4.33.0, although upstream uses 4.35.0-rc2.
No second toolchain or Mathlib checkout is required. The model has finite
workspace, input-independent unitary steps, and a final measurement; these
results do not assert a translation from arbitrary quantum programming languages.

## Operational extraction

`QueryProgram.lean` supplies typed Boolean-oracle programs, adaptive sequencing,
collection of finite estimator families, and candidate verification.
`OperationalExtraction.lean` proves the bucket decoder's exact evaluation and
query sum, followed by at most B verifier runs.

`QuantumExtraction.lean` constructs all B(L+1) bucket and bit-mass estimators
before table sampling, supplies the simultaneous accuracy bound, and proves
`exists_quantum_extractor`. For a q-query native-value quantum algorithm,
a t-heavy valid witness on table mass at least rho, a hash law with collisions
at most 1/B and B*t≥16, and a correct V-query verifier, it supplies a concrete
classical oracle program with success at least rho/2 and query cap

```
B*(L+1)*scalarQueryBudget (2*q+1) (t/16) (rho/(4*B*(L+1))) + B*V.
```

The theorem assumes `hAA`, 0<t,rho≤1, and the stated collision and verifier
hypotheses. It no longer assumes the scalar estimators or their accuracy.

## Tablewise amplification and accepted entropy

`QuantumTablewise.lean` and `XorTablewise.lean` construct one fixed estimator
family outside an exceptional set of oracle tables, then amplify using
independent affine hashes. `SparseAmplification.lean` supplies the sparse-heavy
step; `LogRounding.lean` identifies the operational dyadic exponent with the
ceiling base-two logarithm. Verifier soundness and deterministic query caps are
included, for both query semantics.

`AcceptedEntropy.lean` defines the accepted conditional law and min-entropy and
extracts a heavy valid output from low accepted entropy. `EntropySoundness.lean`
and `XorEntropySoundness.lean` prove the strict exceptional-oracle bound from
`ClassicalSearchSoundness` and the extraction budget. These results are included
in the successful 151-declaration audit. They are generic reductions, not a
formalization of YZ's concrete coding lower bound or seeded extraction.
