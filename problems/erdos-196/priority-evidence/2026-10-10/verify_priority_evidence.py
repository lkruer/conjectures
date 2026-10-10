#!/usr/bin/env python3
"""Recheck captured priority evidence; optionally compare a fresh Discord download.

Offline success verifies consistency and file identity, not a historical timestamp
by itself. The dated claims depend on the separately identified provider records.
"""
import argparse
import base64
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import urllib.parse

PDF_SHA = "b8b5a37349fcbc3d1fa89842ea67b6798dcb58a256998bb6c5064f3a499a7097"
LEAN_SHA = "e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826"
MESSAGE_ID = "1547393457478307970"
ATTACHMENT_ID = "1547393457180643369"
CHANNEL_ID = "1547019042907226143"
ORIGINAL = "8ede860e8fc90a300207a2c17e8aefe6167b3086"
SELECTED = "bf058b903350eb8f873a22ab4a54b2e0faa9727d"
PDF_PATH = "problems/erdos-196/paper/proof.pdf"


def require(ok, message):
    if not ok:
        raise SystemExit("FAIL: " + message)


def stamp(value):
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def snowflake(value):
    milliseconds = (int(value) >> 22) + 1420070400000
    return datetime.fromtimestamp(milliseconds // 1000, timezone.utc).replace(
        microsecond=(milliseconds % 1000) * 1000
    )


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=here.parents[3])
    parser.add_argument("--discord-file", type=Path,
                        help="A freshly downloaded attachment to compare")
    parser.add_argument("--refresh-discord-url",
                        help="Fresh signed URL from the original Discord message")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()
    read = lambda name: json.loads((here / name).read_text())
    message = read("discord-message.json")
    receipt = read("discord-attachment-receipt.json")
    result = read("conjectures-result.json")
    report = read("conjectures-report.json")
    solution = read("conjectures-solution.json")
    competing = read("competing-records.json")
    require(message["message_id"] == MESSAGE_ID, "Message ID")
    require(message["channel_id"] == CHANNEL_ID, "Channel ID")
    require(message["attachment"]["id"] == ATTACHMENT_ID, "Attachment ID")
    path = f"/attachments/{CHANNEL_ID}/{ATTACHMENT_ID}/Erdos196-Kohlmeyer-Kruer.pdf"
    require(urllib.parse.urlparse(message["attachment"]["url"]).path == path,
            "Attachment URL is linked to the identified message")
    msg_time = snowflake(MESSAGE_ID)
    att_time = snowflake(ATTACHMENT_ID)
    require(msg_time == stamp(message["timestamp_utc"]), "Message time and snowflake disagree")
    require(att_time == stamp(receipt["attachment_snowflake_utc"]), "Attachment time disagrees")
    require(att_time <= msg_time, "Attachment is newer than original message")
    headers = receipt["response_headers"]
    modified = parsedate_to_datetime(headers["last-modified"][0])
    require(int(att_time.timestamp()) == int(modified.timestamp()), "CDN date differs")
    require(receipt["status"] == 200 and receipt["curl_exit"] == 0, "Captured download failed")
    require(headers["content-type"][0].split(";")[0] == "application/pdf", "CDN media type")
    pdf = (root / PDF_PATH).read_bytes()
    require(sha(pdf) == PDF_SHA and len(pdf) == 91799, "Submitted PDF identity")
    require(receipt["sha256"] == PDF_SHA and receipt["bytes"] == len(pdf), "Captured PDF identity")
    require(str(len(pdf)) == headers["content-length"][0], "CDN byte length")
    require("md5=" + base64.b64encode(hashlib.md5(pdf).digest()).decode() in headers["x-goog-hash"],
            "CDN content checksum")
    for commit in (ORIGINAL, SELECTED):
        old = subprocess.check_output(["git", "show", f"{commit}:{PDF_PATH}"], cwd=root)
        require(pdf == old, "PDF differs from historical repository version " + commit)
    source = solution["source"].encode("utf-8")
    require(sha(source) == LEAN_SHA and len(source) == 26497, "Service Lean payload identity")
    require(solution["proof_sha256"].removeprefix("sha256:") == LEAN_SHA, "Service proof digest")
    require(solution["byte_length"] == len(source), "Service proof byte length")
    require(result["id"] == solution["id"] == report["id"] ==
            "e73b95f7-1d1b-42b5-a442-c07077741d73", "Service records disagree")
    require(result["verification_status"] == "VERIFIED", "Service verification status")
    require(result["manual_review_status"] == "APPROVED", "Service review status")
    require(report["report"]["accepted"] is True, "Service report rejected")
    require(result["task_id"] == report["report"]["task_id"] ==
            "fc-8432eac9-erdos196-erdos-196-b7454f0edd-counterexample-v1", "Task identity")
    identity_script = root / "problems/erdos-196/verification/2026-10-10/verify_source_identity.py"
    identity = json.loads(subprocess.check_output(
        ["python3", str(identity_script), "--repository", str(root)], cwd=root))
    require(identity["status"] == "PASS" and identity["source_sha256"] == sha(source),
            "Prior selected-proof identity check failed")
    fresh = None
    if args.discord_file:
        require(args.discord_file.read_bytes() == pdf, "Fresh attachment differs")
        fresh = {"kind": "local_download", "matches": True}
    if args.refresh_discord_url:
        url = urllib.parse.urlparse(args.refresh_discord_url)
        require(url.scheme == "https" and url.hostname == "cdn.discordapp.com" and
                url.path == path and not url.username and not url.password,
                "Fresh URL must name the same HTTPS Discord attachment")
        with tempfile.TemporaryDirectory() as tmp:
            body, head = Path(tmp) / "payload.pdf", Path(tmp) / "headers.txt"
            effective = subprocess.check_output([
                "curl", "--proto", "=https", "--proto-redir", "=https", "--location",
                "--fail", "--silent", "--show-error", "--max-time", "30",
                "--output", str(body), "--dump-header", str(head),
                "--write-out", "%{url_effective}", args.refresh_discord_url], text=True)
            final = urllib.parse.urlparse(effective)
            require(final.hostname == "cdn.discordapp.com" and final.path == path,
                    "Fresh download left the identified Discord attachment")
            require(body.read_bytes() == pdf, "Fresh Discord bytes differ")
            modified_lines = [x.split(":", 1)[1].strip() for x in
                              head.read_text().splitlines() if x.lower().startswith("last-modified:")]
            fresh = {"kind": "live_discord_download", "matches": True,
                     "observed_at_utc": datetime.now(timezone.utc).isoformat(),
                     "last_modified": modified_lines[-1] if modified_lines else None}
    verified = stamp(result["verified_at"])
    ho_repo = stamp(competing["ho_github_created_at"])
    ho_arxiv = stamp(competing["ho_arxiv_v1_submitted_at"])
    require(verified < att_time < msg_time < ho_repo < ho_arxiv, "Chronology ordering differs")
    output = {
        "status": "PASS", "pdf_sha256": PDF_SHA, "pdf_bytes": len(pdf),
        "lean_sha256": LEAN_SHA, "lean_bytes": len(source),
        "message_snowflake_utc": msg_time.isoformat(),
        "attachment_snowflake_utc": att_time.isoformat(),
        "cdn_last_modified_utc": modified.isoformat(),
        "conjectures_verified_at": result["verified_at"],
        "same_pdf_in_original_and_selected_commits": True,
        "same_lean_payload_in_service_original_and_selected_proof": True,
        "message_precedes_ho_repository_seconds": (ho_repo - msg_time).total_seconds(),
        "message_precedes_ho_arxiv_seconds": (ho_arxiv - msg_time).total_seconds(),
        "fresh_comparison": fresh,
        "scope": "Consistency and exact file identity. Provider records supply historical dates; this script does not create a timestamp certificate or establish unrestricted public publication."
    }
    text = json.dumps(output, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
