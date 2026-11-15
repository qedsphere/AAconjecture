"""Check audit acceptance/rejection using the actual successful Lean report.

Run after scripts/check.sh:
    uv run --no-project python checks/check_axiom_audit.py
"""
import subprocess
import sys
import re
from pathlib import Path

base = Path("artifacts/axioms.log").read_text()
command = [sys.executable, "scripts/check_axioms.py"]
baseline = subprocess.run(command + ["artifacts/axioms.log"], capture_output=True, text=True)
assert baseline.returncode == 0, baseline.stdout + baseline.stderr
print(baseline.stdout.strip())

axiom_free = re.sub(
    r"'([^']+)' depends on axioms:\s*\[[^]]*\]",
    lambda match: f"'{match.group(1)}' does not depend on any axioms",
    base,
    count=1,
)
axiom_free_path = Path("artifacts/audit-axiom-free-format.log")
axiom_free_path.write_text(axiom_free)
format_check = subprocess.run(command + [str(axiom_free_path)], capture_output=True, text=True)
assert format_check.returncode == 0, format_check.stdout + format_check.stderr
print("PASS: accepted axiom-free report format (parser fixture)")

cases = {
    "placeholder": base.replace("propext", "sorryAx", 1),
    "extra_axiom": base.replace("propext", "UnexpectedAxiom", 1),
    "missing_report": re.sub(r"'[^']+' depends on axioms:\s*\[[^]]*\]|'[^']+' does not depend on any axioms", "", base, count=1),
}
for label, report in cases.items():
    path = Path("artifacts") / f"audit-negative-{label}.log"
    path.write_text(report)
    result = subprocess.run(command + [str(path)], capture_output=True, text=True)
    assert result.returncode != 0, f"Audit incorrectly accepted {label}"
    print(f"PASS: rejected {label}")
