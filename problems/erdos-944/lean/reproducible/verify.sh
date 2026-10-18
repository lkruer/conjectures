#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p verification
python3 - <<'CLEANUP'
from pathlib import Path
for name in ('REPORT.md', 'manifest.json', 'build.log', 'axiom-audit.log', 'cache-get.log', 'lake-version.log', 'lean-version.log'):
    (Path('verification') / name).unlink(missing_ok=True)
Path('SOURCE_SHA256SUMS').unlink(missing_ok=True)
CLEANUP
printf '%s\n' '{"status":"running"}' > verification/status.json
trap 'printf "{\"status\":\"failed\",\"exit_code\":%s}\n" "$?" > verification/status.json' ERR
lake --version | tee verification/lake-version.log
lean --version | tee verification/lean-version.log
lake exe cache get 2>&1 | tee verification/cache-get.log
lake build PrizeSubmission AxiomAudit 2>&1 | tee verification/build.log
lake env lean AxiomAudit.lean 2>&1 | tee verification/axiom-audit.log
python3 write_verification_manifest.py
