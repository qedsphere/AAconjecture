# Lean formalization checkpoint — 2026-11-15

## Target and source

Formalize the results of `/Users/dehmelf/Downloads/unified_aa_simulation.tex`
in Lean 4. The supplied file is a 101-line wrapper, with nine missing inputs
under `results/unified_aa_sections/`. The matching 36-page PDF is available
at `/Users/dehmelf/Downloads/unified_aa_simulation.pdf`. Source SHA-256 hashes,
cached layout text, and a rendering of PDF page 26 are in `artifacts/source/`.
No source files or original PDFs were modified. The PDF is read-only input.

AA is accepted as proved. The supplied upstream formalization is pinned at
`2a6ceaef872ae993708950f951989134084b851a`, using Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. Its public `PrintedConjecture`
is an influential-coordinate statement for bounded multivariate polynomials;
it is not the scalar-estimator decision-tree theorem in manuscript §2.4.
This distinction is a formalization task, not an unresolved AA assumption.

## Precisely stated first question

For arbitrary finite independent table and hash spaces X and H with normalized
nonnegative real weights, output laws p_x on bitstrings of length L, a
table-dependent valid relation R_x, a threshold t > 0, and a hash family with
pair-collision probability at most 1/B where B*t ≥ 16:

* For any designated output y_x, the probability that its bucket's other mass
  exceeds t/4 is at most 1/4.
* If p_x(y_x) ≥ t, and all bucket and bucket-bit estimates have absolute error
  at most t/16, the threshold decoder returns y_x in its bucket.
* If y_x is valid and t-heavy on a table event G of mass at least rho, and for
  each fixed hash simultaneous estimation fails on table mass at most rho/4,
  then the decoded list contains a valid string with joint probability ≥rho/2.

The designated output depends only on the table. Hash and table independence
is encoded by multiplying the two finite laws' weights. Estimation and
isolation failures are not assumed independent. The success event means
existence of a valid candidate in the list, not an executable bounded-query
algorithm that selects it.

## Formalization boundary

This first question is the probability/reconstruction core of Theorem 4.1,
PDF p. 26. It does not yet formalize its quantum/classical query bound.
`UnifiedAA/Influence.lean` separately adapts the supplied AA statement to named
cube variance and flip influence, and derives the manuscript's coarser
epsilon^8/d^12 influence scale from the upstream exponent 7. Its explicit AA
argument is intended to be supplied by the upstream proved theorem. The
large full upstream Main rebuild was stopped at this bounded checkpoint;
no completed local recheck of that proof is claimed.

The remaining manuscript results are not asserted as formalized. In
particular: scalar decision-tree simulation; a quantum query model and its
polynomial method; actual finite affine hashing; bounded-query composition
and verification; tablewise amplification; min-entropy and extraction;
the Gibbs branch; YZ coding and honest quantum preparation; sparse sampling.

See README.md for build status and TODO.md for the ordered remaining work.

## Verification outcome

All four local modules and the aggregate `UnifiedAA.lean` compiled successfully
under Lean 4.33.0. `sh scripts/check.sh` returned exit status 0. Its 13 named
theorem reports (11 extraction results plus two influence statement adapters)
depend only on `propext`, `Classical.choice`, and `Quot.sound`; none uses
`sorryAx` or an additional axiom. The audit checker was also tested against a
passing baseline and reports with a placeholder axiom, an unexpected axiom,
and a missing theorem report. All three malformed reports were rejected.
Reproduce the checker tests with
`uv run --no-project python checks/check_axiom_audit.py` after the Lean audit.
There were no bounded numerical research experiments in this checkpoint.
Logs: `artifacts/check.log`, `artifacts/axioms.log`,
`artifacts/influence-build.log`, and `artifacts/final-build.log`.

The initial full upstream build and a sequential restart were terminated;
no unattended compiler/research loop is left running. The dependency's
compiled statement module and locally compiled adapter are distinguished
from a completed recheck of its Main theorem. No automatic commit was made.

## Second checkpoint: deterministic tree cost and truncation

The next precise question was to justify the scalar simulation proof's
expected-depth and truncation step without assuming that repeated physical
queries behave like independent coins. The new modules are:

- `DecisionTree.lean`: deterministic oracle evaluation, physical query count,
  maximum depth, and K-query truncation using stored real summaries.
- `Uniform.lean`: normalized uniform finite laws and the coordinate-flip
  averaging identity for observables that ignore the queried coordinate.
- `DecisionTreeUniform.lean`: fresh-coordinate trees have exactly the
  fair-branch expected query cost under the uniform Boolean-table law.

For any finite tree t and potential function Phi on subtrees, `HasDrift`
requires nonnegative terminal potentials and, at each query node,
`gamma + (Phi(zero)+Phi(one))/2 ≤ Phi(node)`. Finite induction proves
`gamma * expectedQueries(t) ≤ Phi(t)`. For gamma>0, integer K>0, and a fresh
tree, the truncated tree uses at most K physical queries and changes the
original answer on uniform-table probability at most `Phi(t)/(gamma*K)`.
All three modules compiled; their headline results are included in the
extended publication audit.

Stored summaries are still arbitrary. Polynomial restrictions, the influence
potential identity and upper bound, AA-guided tree construction, exact
conditional-mean leaves, and leaf-error aggregation remain to be proved.
`HasDrift` is explicit; it has not yet been supplied by polynomial AA.

## Publication requested by the user

The user explicitly authorized committing and pushing the progress to
`git@github.com:qedsphere/AAconjecture.git` and asked for a four-person work
plan. That remote already contains paper/research history at
`cdb21b7099c6fefcd9d20108dc33b3b89b7017fd`; its paper hashes match our source
snapshots. Publication adds `formalisation/` and root `PARALLELISATION.md` on
the dedicated `formalisation/lean4-checkpoint` branch, preserving the existing
history and research files. A separate publishing checkout is used because
the local parent workspace has an unborn Git branch and unrelated untracked
files. No unrelated local files need to be overwritten or committed.
