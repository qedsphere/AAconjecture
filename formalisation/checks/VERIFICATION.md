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

Resume with:

```sh
python3 scripts/build_aa_serial.py --start-at AaronsonAmbainis.DetBij.Basic --max-modules 3
# Continue from each printed next module until Main succeeds, then:
lake build UnifiedAA.ProvedAA
lake env lean checks/ProvedAA.lean > artifacts/proved-aa-axioms.log
uv run --no-project python scripts/check_axioms.py artifacts/proved-aa-axioms.log --manifest checks/ProvedAA.lean
```

This is a Lean build and axiom audit, not an independent replay of the entire
Mathlib kernel environment or a proof of correspondence with manuscript prose.
