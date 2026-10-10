# Independent September 9 manuscript evidence

**The complete submitted manuscript was attached to a Discord message sent on September 9, 2026 at 23:49:09.443 UTC. Discord's attachment ID dates the PDF to 23:49:09.372 UTC, and its CDN reports `Last-Modified: Wed, 09 Sep 2026 23:49:09 GMT`. The downloaded PDF is byte-for-byte identical to the manuscript in both the original September 14 upload and the selected JSP proof version.**

This establishes a substantially stronger documented completion claim than the manuscript's internal date or Conjectures.io's retrospective record alone. It independently corroborates possession and transmission of this complete mathematical solution before the identified September 11 competing records.

## Evidence chain

| Record | Observed evidence | Scope |
| --- | --- | --- |
| [Original Discord message](https://discord.com/channels/@me/1547019042907226143/1547393457478307970) | Author `JenWIN`; message ID `1547393457478307970`; DOM timestamp `2026-09-09T23:49:09.443Z`; matching PDF link | Inspected in the author's authenticated Discord session on October 10. Direct message, with access restricted to participants. |
| [Message observation](discord-message.json) and [cropped screenshot](discord-message.jpg) | September 9, 7:49 PM in the author's local display; both named attachments visible | Only the author-supplied message is reproduced. No edited marker was visible; this is an observation, not a complete edit audit. |
| [Discord attachment receipt](discord-attachment-receipt.json) and [selected headers](discord-attachment.headers.txt) | Attachment ID `1547393457180643369`; HTTP 200; 91,799 bytes; matching date, length and checksum metadata | Downloaded from Discord's HTTPS CDN without an account cookie. A second fresh download also matched. |
| [Submitted manuscript](../../paper/proof.pdf) | SHA-256 `b8b5a37349fcbc3d1fa89842ea67b6798dcb58a256998bb6c5064f3a499a7097` | Full byte equality, not a title, screenshot or excerpt match. |
| [Public Conjectures result](conjectures-result.json) | `verified_at: 2026-09-09T23:36:51.116698Z`, `APPROVED`; review decision September 11 | Separate service attestation of earlier formal verification. |
| [Public report](conjectures-report.json) and [accepted source](conjectures-solution.json) | Exact Erdős 196 task; accepted Lean payload SHA-256 `e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826` | Matches the original upload and selected wrapped proof under the previously documented import/namespace-only transformation. |

The seven-page manuscript includes the full negative answer in Theorem 1.1, its finite-extension proof in Sections 2–5 and its construction of the infinite permutation in Section 6. Sections 7 and the acknowledgment record the intended Lean correspondence and assistance. This copy is the already-submitted paper, not a later replacement. The paper's internal creation date is only supporting metadata; the independent evidence is its actual attachment on Discord and the matching provider records.

## Timestamp calculation

Discord [documents its snowflake format](https://docs.discord.com/developers/reference#snowflakes): the upper 42 bits encode milliseconds since January 1, 2015. Integer arithmetic gives:

```python
milliseconds_since_unix_epoch = (int(discord_id) >> 22) + 1420070400000
```

For the message, this gives `2026-09-09T23:49:09.443Z`, exactly the DOM timestamp. For the PDF attachment it gives `2026-09-09T23:49:09.372Z`, 71 milliseconds earlier. The CDN's Last-Modified agrees to its one-second precision. An invented number alone would prove nothing: the check here ties these IDs to a real Discord-served message and PDF, then identifies the exact PDF bytes.

The CDN's `x-goog-generation` is retained as an opaque version identifier. Google [documents generation as an object-version ID](https://docs.cloud.google.com/storage/docs/metadata#generation-number), not a portable timestamp. The signed URL's `is` and `ex` parameters refer to URL issuance and expiry under [Discord's documentation](https://docs.discord.com/developers/reference#signed-attachment-cdn-urls); they are not used as September 9 evidence.

## Comparison with the identified competing records

[Ho's repository metadata](ho-github-repository.json) records creation of `boonsuan/4ap` on September 11 at 00:56:33 UTC. [Ho's arXiv v1](https://arxiv.org/abs/2609.12780v1) records submission at September 11, 12:33:11 UTC. The [comparison record](competing-records.json) preserves sources and dates.

The actual Discord message predates those records by **25 hours, 7 minutes, 23.557 seconds** and **36 hours, 44 minutes, 1.557 seconds**, respectively. These are comparisons to the identified records, not estimates of when Ho privately developed the result. Repository creation alone is not proof of the moment a complete proof was first uploaded. No claim of copying follows.

**Requested finding:** recognize September 9 as the documented completion and third-party transmission date of the Kohlmeyer–Kruer complete solution, and assess mathematical priority from that evidence rather than treating the September 14 public GitHub/forum release as its completion date. See the [formal priority statement](../../PRIORITY.md).

## Reproduce

From a clone containing the original and selected commits:

```sh
python3 problems/erdos-196/priority-evidence/2026-10-10/verify_priority_evidence.py
```

This rechecks the two snowflakes, message/attachment association, header dates and checksums, complete PDF byte identity at both commits, the service's accepted payload and its connection to the selected proof, and the date comparisons. [Recorded results](checks.json) include a second live Discord download. To repeat that download while the URL is valid, use `--refresh-discord-url 'SIGNED_URL'` (requires curl), or download the original attachment and use `--discord-file /path/to/file.pdf`. Discord's signed URLs expire; obtain a fresh one from the same message without changing its attachment ID.

## Evidentiary limits

This package records an independent check of provider-hosted material; it is not a notarization, a provider-signed historical certificate, or an exhaustive audit of Discord's storage. A reviewer can repeat the CDN comparison and participants can inspect the original message. The public files make the evidence inspectable even though the original conversation is private. The screenshot and JSON are supporting captures, not substitutes for the original provider records.

A direct message establishes transmission to its recipient, not unrestricted public publication. The current Prize rules require dated public evidence for a mathematical-priority challenge and use the selected original-repository commit plus supporting history for formalization priority. Whether this private contemporaneous disclosure and its now-public evidence satisfy the mathematical award's requirement is for the organizers to decide. The selected complete Lean proof remains the genuine October 8 commit; no September 9 Git commit is asserted. Earlier unlocated work, universal first discovery and prize entitlement are not established by this bounded comparison.

Conjectures.io's public report is a projection of its complete report: its `report_sha256` identifies the full report, not the reduced public JSON. We do not claim to recompute that full-report digest. The service's public API documents this distinction in [its source](https://github.com/conjectures-io/conjectures-validator/blob/bc4e1f7d5354fbb20d09636399ac24df2b6b63d8/docs/PUBLIC_API.md). Its activity endpoint is derived from the same service database and is not counted as another independent witness.
