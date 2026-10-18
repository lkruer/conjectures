#!/usr/bin/env python3
"""Record a successful verify.sh run. This script never marks a failed run verified."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess

root = Path(__file__).resolve().parent
out = root / 'verification'

def git(*args, cwd=root):
    return subprocess.check_output(['git', *args], cwd=cwd, text=True).strip()

build = (out / 'build.log').read_text()
audit = (out / 'axiom-audit.log').read_text()
if 'Build completed successfully' not in build:
    raise SystemExit('The build log does not record a successful complete build.')
m = re.search(r'PASS: (\d+) proof declarations checked;', audit)
if m is None:
    raise SystemExit('The transitive axiom audit did not record success.')
if 'error:' in audit.lower():
    raise SystemExit('The axiom audit log contains an error.')

manifest = json.loads((root / 'lake-manifest.json').read_text())
packages = []
for p in manifest['packages']:
    actual = git('rev-parse', 'HEAD', cwd=root / '.lake' / 'packages' / p['name'])
    if actual != p['rev']:
        raise SystemExit(f"Dependency revision mismatch: {p['name']}")
    packages.append({'name': p['name'], 'revision': actual, 'url': p['url']})

body = (root / 'accepted-proof-body.lean.txt').read_bytes()
solution = (root / 'Solutions' / 'Erdos944.lean').read_bytes()
if body not in solution:
    raise SystemExit('The recorded accepted proof body is not contained unchanged in Solutions/Erdos944.lean.')
expected = {
    'accepted-proof-body.lean.txt': '8bf7cd0e83463e5f304ad848921c5078d57e8f3411050e705c69a69822abecd5',
    'Solutions/Erdos944.lean': 'f10e4b93691bde98c457e3a95bf8cc92ece6d883dd9795beb92a1d2d7ec343a4',
}
for filename, value in expected.items():
    actual = hashlib.sha256((root / filename).read_bytes()).hexdigest()
    if actual != value:
        raise SystemExit(f'Preserved original source hash mismatch: {filename}')

source_hashes = []
for p in sorted(root.rglob('*')):
    rel = p.relative_to(root)
    if '.lake' in rel.parts or 'verification' in rel.parts or '__pycache__' in rel.parts:
        continue
    if p.is_file() and p.name != 'SOURCE_SHA256SUMS':
        source_hashes.append(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {rel.as_posix()}\n')
hash_text = ''.join(source_hashes)
(root / 'SOURCE_SHA256SUMS').write_text(hash_text)
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
result = {
    'status': 'verified',
    'verified_at_utc': now,
    'repository_commit': git('rev-parse', 'HEAD'),
    'github_sha': os.environ.get('GITHUB_SHA'),
    'github_run_id': os.environ.get('GITHUB_RUN_ID'),
    'github_run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
    'package_path': root.relative_to(Path(git('rev-parse', '--show-toplevel'))).as_posix(),
    'source_manifest_sha256': hashlib.sha256(hash_text.encode()).hexdigest(),
    'platform': platform.platform(),
    'lean_version': (out / 'lean-version.log').read_text().strip(),
    'lake_version': (out / 'lake-version.log').read_text().strip(),
    'proof_declarations_audited': int(m[1]),
    'permitted_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'additional_axioms_or_sorryAx': False,
    'dependencies': packages,
    'commands': ['lake exe cache get', 'lake build PrizeSubmission AxiomAudit', 'lake env lean AxiomAudit.lean'],
    'original_source_commit': 'caa0b07847cc94a071215de82036be4b5805ee0c',
    'original_source_hashes': expected,
}
(out / 'manifest.json').write_text(json.dumps(result, indent=2) + '\n')
(out / 'status.json').write_text(json.dumps({'status': 'verified', 'verified_at_utc': now}, indent=2) + '\n')
(out / 'REPORT.md').write_text(f'''# Erdős 944 Lean verification

Result: **verified** at {now}.

- Repository commit: `{result['repository_commit']}`.
- Source manifest SHA-256: `{result['source_manifest_sha256']}` (`SOURCE_SHA256SUMS`).
- Lean: `{result['lean_version']}`.
- Pinned mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Targeted build: `lake build PrizeSubmission AxiomAudit` succeeded.
- Transitive axiom audit: **{result['proof_declarations_audited']} declarations passed**; no `sorryAx` or additional axioms. The permitted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`Erdos944Prize.target` explicitly proves the requested finite graph exists for every `k ≥ 4` and `r ≥ 1`; `finite_all` also covers `r = 0`. `benchmark_type_check` has exactly the elaborated original Formal Conjectures type. The imported problem stub contains placeholders, but the successful audit establishes that the proof does not depend on them.

The original accepted proof body and its `Solutions/Erdos944.lean` wrapper matched their recorded source hashes. This is a successful Lean build and dependency audit, not a prize-award or priority decision. Full command output and all dependency revisions are retained beside this report.
''')
print(f"Verification manifest written for {result['repository_commit']}; {result['proof_declarations_audited']} declarations audited.")
