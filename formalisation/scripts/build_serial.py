"""Build project and vendored modules in dependency order, one Lean job at a time.

Run from formalisation/. Fetch the documented targeted Mathlib cache first, or
pass --cache to fetch all directly imported Mathlib modules and their closure.
"""
import argparse
import re
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--cache", action="store_true")
parser.add_argument("targets", nargs="*", help="Optional root modules; default: all local and vendored modules")
args = parser.parse_args()

sources = {"UnifiedAA": Path("UnifiedAA.lean")}
for root in (Path("."), Path("vendor/quantum-query-complexity")):
    namespace = "UnifiedAA" if root == Path(".") else "QuantumQueryComplexity"
    for path in (root / namespace).rglob("*.lean"):
        sources[".".join(path.relative_to(root).with_suffix("").parts)] = path

def source_imports(path):
    """Ignore nested Lean comments before looking for module imports."""
    source = path.read_text()
    output, depth, index = [], 0, 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif not depth and source.startswith("--", index):
            index = source.find("\n", index)
            if index < 0:
                break
        else:
            char = source[index]
            output.append(char if not depth or char == "\n" else " ")
            index += 1
    return re.findall(r"^(?:public\s+)?import\s+(\S+)", "".join(output), flags=re.MULTILINE)


imports = {name: source_imports(path) for name, path in sources.items()}
order, active, done = [], set(), set()


def visit(name):
    if name in done:
        return
    if name in active:
        raise SystemExit(f"Import cycle at {name}")
    active.add(name)
    for dependency in imports[name]:
        # Check each referenced AA proof module separately as well. Otherwise
        # Lake could compile several previously unbuilt AA dependencies at once.
        if dependency.startswith("AaronsonAmbainis.") and dependency not in sources:
            path = Path(".lake/packages/AaronsonAmbainis") / (
                dependency.replace(".", "/") + ".lean")
            sources[dependency] = path
            imports[dependency] = source_imports(path)
        if dependency in sources:
            visit(dependency)
    active.remove(name)
    done.add(name)
    order.append(name)


for name in (args.targets or sorted(list(sources))):
    if name not in sources:
        raise SystemExit(f"Unknown target: {name}")
    visit(name)

if args.cache:
    mathlib = {imp for name in order for imp in imports[name] if imp.startswith("Mathlib.")}
    subprocess.run(["lake", "exe", "cache", "get", *sorted(mathlib)], check=True)

for name in order:
    print(f"Checking {name}", flush=True)
    subprocess.run(["lake", "build", name], check=True)

