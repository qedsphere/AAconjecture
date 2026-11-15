# Evidence for the event-report format revision

Prepared 2026-11-15. This directory documents support for claims; it does not
establish which activities took place during the event. The event's exact
40-hour interval and complete contributor attribution remain unconfirmed.

## Manuscript revision

`before-format.tex` preserves the standalone manuscript before restructuring.
The root `unified_aa_simulation.tex` is the edited report. The revision adds
a short abstract, reading guide, claim-support ledger in section 5, event
accounting, limitations, and named AI/source/help acknowledgements. It retains
the mathematical proof sections. The prose and evidence organization are not
new mathematical results.

## Saved Lean evidence

The following files were copied read-only from the sibling integration checkout
`/Users/dehmelf/Research/AA-conjecture-integration/formalisation/`:

- `checks/Axioms.lean` -> `Axioms.lean`
- `artifacts/axioms.log` -> `axioms.log`
- `scripts/check_axioms.py` -> `check_axioms.py`
- `checks/VERIFICATION.md` -> `VERIFICATION.md`
- `checks/WholeProofCoverage.md` -> `WholeProofCoverage.md`

The checkout HEAD at collection was
`60bede3c633b01f62c7d2dadfac80e9654fab405`; the checkout also contained
uncommitted work. That commit alone does not identify the saved checkpoint.
The exact manifest/log hashes below identify the audited evidence, and the
coverage documents state its recorded build status. Full reproduction requires
the matching Lean source snapshot and pinned dependencies; copying these
records does not reproduce the kernel build or package all 286 theorem sources.

SHA-256:

```text
1452851a628707a806f6fb32c20e254ebd1d139b622a946eff652be68d47fb32  Axioms.lean
a0442e0567345353e0ee4679d4066c219d0996ed1ad9b4b561ef92dff7e72c49  axioms.log
```

Command rerun from the workspace root:

```sh
uv run --no-project python artifacts/event-report-evidence/check_axioms.py --manifest artifacts/event-report-evidence/Axioms.lean artifacts/event-report-evidence/axioms.log
```

Outcome: `PASS: 286 theorems; only Classical.choice, Quot.sound, propext`.
Output: `audit-recheck.txt`. This validates the saved report against the
explicit manifest; it is not a fresh Lean build. The recorded checkpoint uses
Lean 4.33.0, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, and external
AA `2a6ceaef872ae993708950f951989134084b851a`. External AA remains a proved
input and was not rebuilt. Coverage is partial, as detailed in the report.

## Finite computations rerun

```sh
uv run --no-sync pytest -q checks/test_preimage_preparation.py checks/test_yz_list_recovery.py
```

Outcome: **26 passed in 0.60s**. Saved output: `computation.txt`.
Python 3.12.9, pytest 9.2.0, macOS 26.1 ARM64; see `environment.txt`.
No random seed is needed: these checks enumerate the specified finite cases
and use exact integers/rationals for the research calculations.

The preparation tests enumerate all Boolean tables of sizes 1, 2, 4, and 8;
tensor families (size, coordinates) = (2,2), (2,3), (4,2); and all 3-bit cell
values, selected answer-bit positions, and dummy bits. They check phase and
diffusion coefficients, normalization, leakage, uniform averages, tensor
budgets, and negative/edge cases. They do not simulate a code decoder.

The list-recovery tests check the two source inequalities and verification
slack at b=22..26 with rate 7/8, plus b=26 with rates 9/10 and 15/16. They
retain b=20,21 as verification-budget failures, rounding checks at
b in {22,24,26} with rates in {7/8,9/10,15/16}, a small cleared-denominator
example, and the b=28 size-guard rejection. The asymptotic result is supported
by the manuscript's written proof, not by these finite instances.

The publication includes the two test files, their helper modules in
`scripts/`, and the project's `pyproject.toml`/`uv.lock` so these checks are
reproducible. In a fresh checkout, run `uv sync --frozen` before the test
command above. The older intermediate `layout-*.png` renders are retained
locally; the final `final-layout-*.png` inspection sheets are published.
When publishing, the support prose was clarified to acknowledge the separate
hard-sector formalization modules now present on remote `main`. They are not
part of the saved 286-declaration audit and were not re-audited in this session.

## PDF build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=artifacts/tex-build/unified-pdflatex unified_aa_simulation.tex
```

Compiler diagnostics, page count, visual inspection, and proof-preservation
checks are recorded after the build below. Compilation does not verify the
mathematics or establish event eligibility.

Final outcome: **50 pages**, successful pdfTeX 1.40.29 (TeX Live 2026) build,
with no compiler warnings, overfull boxes, missing characters, or unresolved
references/citations in the final log. Section 5 is the claim-support and Lean
section. Exact comparisons confirmed that all 16 theorem, 11 lemma,
7 proposition, 2 corollary, 31 proof, and 7 open-problem blocks were unchanged.
The final front matter, ledgers, disclosures, and evidence appendix were
rendered and visually inspected (pages 1, 5, 34–37, 43–47, and 50).
`proof-preservation.txt`, `build.json`, and `final-layout-*.png` record these
checks. `unified_aa_simulation.pdf` at the workspace root is the final PDF.
The earlier `layout-*.png` files show the intermediate pagination before
major-section page breaks were added.

## Publication checkout verification

The report was prepared for publication in an isolated checkout based on
remote `main` at `4be1ca7`, preserving the newer hard-sector modules there.
`uv sync --frozen` succeeded in that checkout. The same two test files then
passed **26 cases in 0.62s**, and the explicit-manifest saved-audit check
passed for all **286 declarations**. This rerun used Python 3.14.0 and pytest
9.2.0 on macOS ARM64; the original report-formatting run above used Python
3.12.9. See `publication-checks.txt`, `publication-audit.txt`, and
`publication-environment.txt`. The final PDF still has 50 pages and no TeX
warnings; its hashes in `build.json` include the publication clarification
about the separately maintained hard-sector formalization. No Lean proof
source was changed by this publication.
