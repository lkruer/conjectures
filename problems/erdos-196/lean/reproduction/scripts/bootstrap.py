#!/usr/bin/env python3
"""Reconstruct the original validator's exact Formal Conjectures commit."""
from pathlib import Path
import hashlib
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
DEST = ROOT / ".dependencies" / "formal-conjectures"
BASE = "7d1a8c9912747679d0093f6d1216420c33ee5ffa"
PIN = "8432eac998110a563e03df65a28c117e97c8c142"
TREE = "88827a7ca9495954133c8549ea5e9d86acc7325a"
PATCH_SHA256 = "d1a2c6dac5ea42366b6ceebcf2f57339c4fb29c4264ec3674065f025a0b30bae"

def run(*args, cwd=None, data=None):
    return subprocess.check_output(args, cwd=cwd, input=data).decode().strip()

if DEST.exists():
    assert run("git", "rev-parse", "HEAD", cwd=DEST) == PIN, "Unexpected dependency revision"
    assert not run("git", "status", "--porcelain", "--untracked-files=no", cwd=DEST), "Dependency has local changes"
    print("Pinned Formal Conjectures already present:", PIN)
else:
    DEST.parent.mkdir(parents=True, exist_ok=True)
    patch = ROOT / "provenance" / "formal-conjectures.patch"
    assert hashlib.sha256(patch.read_bytes()).hexdigest() == PATCH_SHA256
    with tempfile.TemporaryDirectory(prefix="fc-bootstrap-", dir=DEST.parent) as scratch:
        checkout = Path(scratch) / "checkout"
        run("git", "init", str(checkout))
        run("git", "remote", "add", "origin", "https://github.com/google-deepmind/formal-conjectures.git", cwd=checkout)
        run("git", "fetch", "--depth=1", "origin", BASE, cwd=checkout)
        run("git", "checkout", "--detach", "FETCH_HEAD", cwd=checkout)
        run("git", "apply", "--index", str(patch), cwd=checkout)
        assert run("git", "write-tree", cwd=checkout) == TREE
        raw_commit = (ROOT / "provenance" / "formal-conjectures-commit.txt").read_bytes()
        assert run("git", "hash-object", "-t", "commit", "-w", "--stdin", cwd=checkout, data=raw_commit) == PIN
        run("git", "checkout", "--detach", PIN, cwd=checkout)
        checkout.rename(DEST)
    print("Reconstructed exact Formal Conjectures commit:", PIN)
