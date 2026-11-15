#!/bin/sh
# Run from formalisation/. Standard Lean/Mathlib axioms are allowed; sorryAx
# and any additional axioms cause this audit to fail.
set -eu
mkdir -p artifacts
python3 scripts/build_serial.py
lake env lean checks/Axioms.lean > artifacts/axioms.log
uv run --no-project python scripts/check_axioms.py artifacts/axioms.log
