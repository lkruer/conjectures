# Erdős 196 completion and priority submission

**We claim completion of the full formal counterexample by the service's recorded September 9, 2026 verification, and request that this evidence be considered when adjudicating mathematical and formalization priority.** The claim rests on an external verification record linked to the same proof, in addition to the manuscript's internal date. First public disclosure and the Prize's formalization-commit rule require separate findings.

## Dated evidence

| Event | Evidence and scope |
| --- | --- |
| September 9, 2026 | The [Conjectures.io result](https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73) records successful verification for JenW1N. The current public record also links the accepted source. |
| September 10 | That record reports a fresh isolated replay of the exact accepted proof and task. |
| September 11 | The service records its approval decision. This is a service decision, distinct from Prize acceptance or a determination of originality. |
| September 11, 00:56:33 UTC | GitHub records creation of [Boon Suan Ho's 4ap repository](https://github.com/boonsuan/4ap); the observed initial commit is `057d19da7abd21c91b46fe5194c9c32789fa62c8`. |
| September 11, 12:33:11 UTC | Ho's [arXiv v1](https://arxiv.org/abs/2609.12780v1) records submission of the same full negative answer. |
| September 14 | Conjectures.io dates certification/publication of its result. This is later than its recorded verification. |
| September 14, 03:39:34 UTC | The [initial original-repository commit](https://github.com/lkruer/conjectures/commit/8ede860e8fc90a300207a2c17e8aefe6167b3086) contains the same Lean payload. This is a recorded Git date, not independently sufficient proof of first publication time. |
| September 14 | [Public proof claim 311](https://www.erdosproblems.com/forum/thread/196/proof-claims#proof-claim-311) credits Liam Kruer and Jensen Kohlmeyer. |
| October 8 | The selected reproducible proof commit `bf058b903350eb8f873a22ab4a54b2e0faa9727d` preserves that payload and adds the task wrapper and direct corollary. |
| October 10 | [Fresh verification](verification/2026-10-10/report.md) passes source compilation, exact statements, all seven axiom audits, kernel replay and independent Nanoda checks. |

Dates without times are preserved at the precision displayed by the source. We do not assign them a time zone or invent an earlier Git commit.

## Checkable connection to the accepted proof

The [accepted-source download](https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73/solution/download) captured during the October 10 review is 26,497 bytes. Its SHA-256 is:

```text
e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826
```

It is byte-for-byte identical to all of the following:

- [The file in the original September 14 commit](https://github.com/lkruer/conjectures/blob/8ede860e8fc90a300207a2c17e8aefe6167b3086/problems/erdos-196/lean/Erdos196.lean).
- [The preserved submission payload at the selected proof commit](https://github.com/lkruer/conjectures/blob/bf058b903350eb8f873a22ab4a54b2e0faa9727d/problems/erdos-196/lean/reproduction/originals/Erdos196-submission.lean).
- The checked `Erdos196.lean` after removing only its two imports and outer `Bounty` namespace wrapper. No mathematical proof line is removed or changed.

The [identity-check script](verification/2026-10-10/verify_source_identity.py), [machine-readable result](verification/2026-10-10/source-identity-result.json) and [evidence manifest](verification/2026-10-10/priority-evidence.json) make this comparison reproducible. Supply a newly downloaded file using `--service-file PATH` to compare it too. Hash equality verifies source identity; it does not timestamp the file or authenticate the service's historical logs.

The service result lists JenW1N. The joint authorship claim for Jensen Kohlmeyer and Liam Kruer is separately supported by the preserved manuscript and public author claim; it is not inferred from the service account or repository ownership alone.

## Requested priority findings

1. **Completion:** Consider September 9 as the claimed completion date of this full formal result, supported by the service record and exact-source linkage. This precedes the September 11 competing records identified above.
2. **Mathematical contribution:** Assess that evidence together with the manuscript, construction, authorship and competing publications. The September 14 public release should not be mistaken for the only evidence of when the proof was completed.
3. **Lean formalization:** Apply the Prize's [selected-commit and corroborating-history rules](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/docs/award-process.md#lean-formalization-or-both-roles) separately. The selected repository commit remains the actual October 8 commit. We request consideration of the earlier service-attested proof, not that the October commit be treated as a September 9 Git commit.

The current service page is retrospective public evidence of earlier events, not proof that the complete solution was publicly accessible on September 9. Its underlying dated records remain for the organizers to authenticate. Ho's earlier public disclosure is retained explicitly. The chronology alone does not establish independence or copying in either direction, and our verification did not independently compile Ho's code. First-publication priority and award entitlement are not claimed as settled.
