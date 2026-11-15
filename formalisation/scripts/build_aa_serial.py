"""Check the pinned AA Main dependency closure, one module at a time.

Apply patches/aa-proof-imports.patch and fetch its targeted Mathlib cache first.
This script never imports the larger upstream aggregate library.
"""
import re
import subprocess
import argparse
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--queue", type=Path, help="Optional ordered local targets, checked between AA modules")
args = parser.parse_args()
root = Path(".lake/packages/AaronsonAmbainis")
order, active, done = [], set(), set()


def strip_comments(source):
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
    return "".join(output)


def visit(name):
    if name in done:
        return
    if name in active:
        raise SystemExit(f"Import cycle at {name}")
    active.add(name)
    path = root / (name.replace(".", "/") + ".lean")
    source = strip_comments(path.read_text())
    for dependency in re.findall(r"^import\s+(\S+)", source, flags=re.MULTILINE):
        if dependency.startswith("AaronsonAmbainis."):
            visit(dependency)
    active.remove(name)
    done.add(name)
    order.append(name)


visit("AaronsonAmbainis.Main")
print(f"AA proof closure: {len(order)} modules", flush=True)
checked_local = set()
for index, name in enumerate(order, start=1):
    if args.queue and args.queue.exists():
        for target in args.queue.read_text().splitlines():
            target = target.strip()
            if not target or target.startswith("#") or target in checked_local:
                continue
            if not re.fullmatch(r"UnifiedAA(?:\.[A-Za-z_][A-Za-z_0-9]*)*", target):
                raise SystemExit(f"Invalid local target: {target!r}")
            print(f"Checking local target: {target}", flush=True)
            subprocess.run(["lake", "build", target], check=True)
            checked_local.add(target)
    print(f"Checking {index}/{len(order)}: {name}", flush=True)
    subprocess.run(["lake", "build", name], check=True)
