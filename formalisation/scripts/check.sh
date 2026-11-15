#!/bin/sh
# Run from formalisation/. Audit the certified-randomness aggregate, optionally
# including the full pinned AA proof and the corollaries with no hAA argument.
set -eu
case "${1-}" in
  "") target=UnifiedAA ;;
  --proved-aa) target=UnifiedAA.ProvedAA ;;
  *) echo "Usage: sh scripts/check.sh [--proved-aa]" >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: sh scripts/check.sh [--proved-aa]" >&2
  exit 2
fi
mkdir -p artifacts
if [ "$target" = UnifiedAA.ProvedAA ]; then
  python3 scripts/build_serial.py UnifiedAA "$target"
else
  python3 scripts/build_serial.py "$target"
fi
lake env lean checks/Axioms.lean > artifacts/axioms.log
uv run --no-project python scripts/check_axioms.py artifacts/axioms.log
if [ "$target" = UnifiedAA.ProvedAA ]; then
  lake env lean checks/ProvedAA.lean > artifacts/proved-aa-axioms.log
  uv run --no-project python scripts/check_axioms.py artifacts/proved-aa-axioms.log \
    --manifest checks/ProvedAA.lean
fi
