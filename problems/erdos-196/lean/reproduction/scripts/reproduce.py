#!/usr/bin/env python3
"""Fetch pinned dependencies, compile the proof, and reject unexpected axioms."""
from pathlib import Path
import argparse
import datetime
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser()
parser.add_argument("--skip-cache", action="store_true", help="Use already installed dependency artifacts")
args = parser.parse_args()
LOGS = ROOT / "reproduction-logs"
LOGS.mkdir(exist_ok=True)
results = []

def run(name, command):
    print("Running:", " ".join(command), flush=True)
    proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (LOGS / (name + ".log")).write_text(proc.stdout)
    print(proc.stdout, end="", flush=True)
    results.append({"step": name, "command": command, "exit_code": proc.returncode})
    (LOGS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    if proc.returncode:
        raise SystemExit(proc.returncode)
    return proc.stdout

run("bootstrap", [sys.executable, "scripts/bootstrap.py"])
run("version", ["lake", "env", "lean", "--version"])
if not args.skip_cache:
    run("cache", ["lake", "exe", "cache", "get"])
run("utilities", ["lake", "build", "FormalConjecturesUtil", "TaskSupport"])
# The pinned project also defines an AnswerPostpone library over the same modules.
# Compile this declaration explicitly in the original validator's always_true mode.
fc = ".dependencies/formal-conjectures"
fc_output = fc + "/.lake/build/lib/lean/FormalConjectures/ErdosProblems/196.olean"
(ROOT / fc_output).parent.mkdir(parents=True, exist_ok=True)
run("statement", ["lake", "env", "lean", "--root=" + fc, "-Dgoogle.answer=always_true", "-o", fc_output,
    fc + "/FormalConjectures/ErdosProblems/196.lean"])
for module in ["Erdos196", "PaperMain"]:
    run(module, ["lake", "env", "lean", "-o", ".lake/build/lib/lean/" + module + ".olean", module + ".lean"])
audit = run("audit", ["lake", "env", "lean", "--trust=0", "Audit.lean"])
expected = {
    "Bounty.target", "Bounty.paper_main", "Bounty.Construction196.counterexample",
    "Bounty.Construction196.finite_extension", "Bounty.Construction196.permFun_injective",
    "Bounty.Construction196.permFun_surjective", "Bounty.Construction196.permFun_no_four",
}
seen = {}
for theorem, axiom_text in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
    axioms = {a.strip() for a in axiom_text.split(",") if a.strip()}
    assert axioms == {"propext", "Classical.choice", "Quot.sound"}, (theorem, axioms)
    seen[theorem] = sorted(axioms)
assert set(seen) == expected, ("Missing or unexpected audit declarations", seen)
report = {"status": "passed", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "axioms": seen}
(LOGS / "audit-result.json").write_text(json.dumps(report, indent=2) + "\n")
print("Build and axiom audit passed.")
