#!/usr/bin/env python3
"""Check the accepted-source linkage; this does not authenticate historical dates."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--service-file", type=Path, default=here / "service-download.lean")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()
    original = "8ede860e8fc90a300207a2c17e8aefe6167b3086"
    selected = "bf058b903350eb8f873a22ab4a54b2e0faa9727d"
    original_path = "problems/erdos-196/lean/Erdos196.lean"
    selected_dir = "problems/erdos-196/lean/reproduction/"
    expected = "e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826"

    def git_bytes(commit, path):
        return subprocess.check_output(["git", "show", commit + ":" + path], cwd=root)

    def require(condition, message):
        if not condition:
            raise SystemExit(message)

    service = args.service_file.read_bytes()
    sha = hashlib.sha256(service).hexdigest()
    require(sha == expected, "Accepted-source SHA-256 differs from the recorded source")
    require(service == git_bytes(original, original_path), "Original Git object differs")
    payload = git_bytes(selected, selected_dir + "originals/Erdos196-submission.lean")
    require(service == payload, "Selected preserved payload differs")
    require(service == (root / original_path).read_bytes(), "Current original payload differs")

    wrapped = git_bytes(selected, selected_dir + "Erdos196.lean")
    prefix = "import FormalConjectures.ErdosProblems.«196»\nimport TaskSupport\n\n".encode()
    require(wrapped.startswith(prefix), "Unexpected wrapper imports")
    unwrapped = wrapped[len(prefix):]
    marker = b"\nnamespace Bounty\n\n"
    require(unwrapped.count(marker) == 1, "Unexpected outer namespace")
    pos = unwrapped.index(marker)
    unwrapped = unwrapped[:pos] + unwrapped[pos:].replace(marker, b"", 1)
    suffix = b"\nend Bounty\n"
    require(unwrapped.endswith(suffix), "Unexpected outer namespace ending")
    unwrapped = unwrapped[:-len(suffix)]
    require(unwrapped == service, "Wrapped proof changes the submitted payload")

    checked = json.loads((here / "source-hashes.json").read_text())
    for path, digest in checked.items():
        historical = git_bytes(selected, path)
        require(hashlib.sha256(historical).hexdigest() == digest, "Selected source hash differs: " + path)
        require((root / path).read_bytes() == historical, "Current audited source differs: " + path)
    result = {
        "status": "PASS",
        "source_sha256": sha,
        "source_bytes": len(service),
        "original_commit": original,
        "original_path": original_path,
        "selected_proof_commit": selected,
        "original_git_object_equals_service_download": True,
        "selected_preserved_payload_equals_service_download": True,
        "wrapped_proof_minus_only_imports_and_outer_namespace_equals_service_download": True,
        "all_audited_sources_still_match_selected_commit": True,
        "audited_files_checked": len(checked),
        "historical_date_authenticated_by_this_script": False,
        "scope": "Byte identity only. The service's historical dates require separate authentication.",
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
