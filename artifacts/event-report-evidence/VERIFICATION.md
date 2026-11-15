# Current aggregate verification — 286 declarations

## Current verified checkpoint

The aggregate `UnifiedAA` build passed, and all **286 selected declarations**
in `checks/Axioms.lean` passed the exact-set axiom audit using only
`propext`, `Classical.choice`, and `Quot.sound`. Negative parser fixtures
rejected placeholders, unexpected axioms, and missing reports. Logs:
`artifacts/expanded-aggregate-build.log` and `artifacts/axioms.log`.

This includes scalar simulation and native/XOR extraction/entropy, per-table
and global accepted-output seeded hashing, exact honest preimage-state and
sharp measurement bounds, Gibbs probability/query-cap infrastructure, and
the complete **native-oracle sparse-sampling** construction with affine banks,
actual programs, fallback, tablewise TV, query cost and bank-size bounds.

External AA is a proved theorem supplied as `hAA`; rebuilding its proof is
excluded by user instruction. The whole manuscript is **not yet formalized**.
Concrete YZ L1/L2 feasibility, adaptive coding soundness and entropy scales,
full honest generation/resources, and Gibbs history/posterior/product-alphabet
assemblies remain. `checks/WholeProofCoverage.md` is the detailed ledger.
The ordinary-XOR sparse sampler, biased restriction/smoothness, deferred-bit
interfaces, and the agents' remaining modules are source drafts until built
and audited. No new work was committed or pushed in this checkpoint.

Manifest SHA-256: `1452851a628707a806f6fb32c20e254ebd1d139b622a946eff652be68d47fb32`.
Actual axiom-report SHA-256: `a0442e0567345353e0ee4679d4066c219d0996ed1ad9b4b561ef92dff7e72c49`.

Commands completed successfully:

```sh
lake build UnifiedAA
lake env lean checks/Axioms.lean > artifacts/axioms.log 2>&1
uv run --no-project python scripts/check_axioms.py artifacts/axioms.log
uv run --no-project python checks/check_axiom_audit.py
```

The current aggregate excludes draft modules and external AA proof rebuilding.
The reported audit is a dependency audit of the named declarations, not an
independent replay of all Mathlib or a proof that every manuscript claim has
been represented.

## Historical verification records (superseded by current status)

# Verification checkpoint — 2026-11-15

Base commit: `cc29b4b`. Toolchain: Lean 4.33.0.
AA dependency: `2a6ceaef872ae993708950f951989134084b851a`.
Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Only the tracked import-line patches were applied to AA; proof bodies and
statements were not changed.

## Checked core

Command: `sh scripts/check.sh` (exit status 0).

```text
PASS: 151 theorems; only Classical.choice, Quot.sound, propext
```

The audit covers the exact declarations listed in `checks/Axioms.lean`,
including native/XOR affine extraction, bucket rounding, tablewise and sparse
amplification, and the generic accepted-entropy soundness contradiction.
These theorems retain the explicit AA proof argument and their documented
verifier, soundness and budget hypotheses. They do not instantiate YZ coding
soundness or prove seeded extraction. Other Gibbs/hard-sector work is outside
this checkpoint's checked core.

Command: `uv run --no-project python checks/check_axiom_audit.py` (exit status 0).
The checker accepted the actual baseline and axiom-free format fixture, and
rejected placeholder axioms, unexpected axioms, and a missing theorem report.
This checks the audit parser, not additional mathematical theorems.

Manifest SHA-256: `a7a6675a76ac7418ca362afab765ca4be3379620884fb342bbf8ec542fff4d47`.
Actual Lean axiom-report SHA-256: `ea8f8d66a864bf4559cc46653b4d4c601108b454e57f447d7debdf3899eb0ee0`.
The raw logs are retained locally under `artifacts/`; rerunning the commands
regenerates them. Exact log bytes may differ with diagnostics and whitespace.

## Not yet checked

The upstream AA build passed the first 10/74 modules, through
`AaronsonAmbainis.DetLow.Main`. `AaronsonAmbainis.DetBij.Basic` is next.
The first long driver ended without a diagnostic; the isolated retry of
`DetLow.NonZero` passed. Bounded subsequent batches reached module 10.

`UnifiedAA/ProvedAA.lean` contains nine draft corollaries using the proved
upstream theorem. They have not yet been compiled or audited. The full Main
proof has not been checked locally. `checks/ProvedAA.lean` lists the ten
pending reports. No compiler is left running at this publication boundary.

The upstream resume commands from the publication checkpoint are superseded:
the user explicitly excluded further external AA proof rebuilding. Continue
our results with the proved AA statement supplied as the explicit `hAA` input.

This is a Lean build and axiom audit, not an independent replay of the entire
Mathlib kernel environment or a proof of correspondence with manuscript prose.

## Subsequent checkpoint: global acceptance reweighting

Per user instruction, external AA proof rebuilding is no longer in scope.
The next completed target is `AcceptanceReweighting.lean`, which proves the
p. 27 joint TV bound with actual accepted-table side information. The per-table
extraction guarantee remains an input; seeded leftover hashing is not yet proved.

Commands `lake build UnifiedAA.AcceptanceReweighting` and `lake build UnifiedAA`
passed. `lake env lean checks/Axioms.lean` and the exact-set checker now pass
**157 declarations**. The audit-checker negative fixtures passed again. The six
new declarations also passed their independent manifest audit. All reports use
only `propext`, `Classical.choice`, and `Quot.sound`.

Updated manifest SHA-256: `8b43404e02d76f04036b49727feb0976647ba552fa0728a790713fda99d2ac73`.
Updated actual axiom report SHA-256: `11396e09825ee583d70247acc5abdb0e432d225f51d1e60578d4be2c1a34ffe0`.
Logs: `artifacts/acceptance-reweighting-build.log`,
`artifacts/acceptance-reweighting-axioms.log`,
`artifacts/reweighting-aggregate-build.log`, `artifacts/axioms.log`, and
`artifacts/reweighting-audit-checker.log`. No upstream AA module was compiled
for this result, and no compiler is left running at this checkpoint.
