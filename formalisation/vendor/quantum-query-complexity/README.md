# Selected quantum-query infrastructure

Source: https://github.com/troyjlee/quantum-query-complexity

Pinned source commit: `df7f2e8199bd845a35a4200e0c74d964ec6b02b8`.
Author: Troy Lee. License: Apache-2.0 (included as `LICENSE`).

Only the twelve-module dependency closure of `Quantum.PolynomialMethod`,
`Quantum.XorPolynomialMethod`, and `Quantum.Postcomp` is vendored. It supplies
finite quantum states, value and padded-XOR oracle models, fixed output
postprocessing, measurement probabilities, and their degree-2q polynomial
representations.
Upstream uses Lean 4.35.0-rc2. All twelve modules compiled unchanged against
this project's Lean 4.33.0 and pinned Mathlib on 2026-11-15. The copied Lean
files match that commit byte for byte; no compatibility edits were needed.

`UnifiedAA.QuantumSimulation` uses these operational semantics to obtain the
degree bound and then apply the local AA-conditional scalar estimator.
No upstream compiled artifacts or second Mathlib checkout are included.
Build sequentially with `python3 scripts/build_serial.py`; the initial build
record is in `artifacts/build-quantum.log`.
