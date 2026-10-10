# Erdős 196 completion and priority claim

**Jensen Kohlmeyer and Liam Kruer claim priority for their complete mathematical solution of Erdős 196, documented as completed and transmitted by September 9, 2026 at 23:49:09 UTC. Independent Discord evidence now corroborates that date: the actual message contains a PDF byte-for-byte identical to the submitted complete manuscript, and Discord's message ID, attachment ID and CDN Last-Modified agree. This predates the identified September 11 records for Boon Suan Ho's solution.**

The claim is supported by the [independent evidence package](priority-evidence/2026-10-10/README.md), [original message](https://discord.com/channels/@me/1547019042907226143/1547393457478307970), [message observation](priority-evidence/2026-10-10/discord-message.json), [CDN receipt](priority-evidence/2026-10-10/discord-attachment-receipt.json) and [passing reproducible checks](priority-evidence/2026-10-10/checks.json). The message is a private direct message, so we distinguish documented completion and transmission from unrestricted public release. Mathematical and Lean award priority require separate findings under the Prize rules.

## Dated evidence

| Event | Evidence and scope |
| --- | --- |
| September 9, 23:36:51.116698 UTC | [Conjectures.io public result](https://conjectures.io/v1/results/e73b95f7-1d1b-42b5-a442-c07077741d73) records successful verification for JenW1N. The accepted source is identical to the preserved submission payload. |
| September 9, 23:49:09.372 UTC | Discord PDF attachment `1547393457180643369` was created under its snowflake timestamp. CDN Last-Modified is September 9 at 23:49:09 UTC; a direct HTTPS download yields the exact complete manuscript. |
| September 9, 23:49:09.443 UTC | Discord message `1547393457478307970`, by JenWIN, contains that attachment. Its displayed date, DOM timestamp and snowflake match. The message documents transmission to another person. |
| September 10 | The Conjectures result reports an isolated replay of the accepted proof and task. |
| September 11, 00:56:33 UTC | GitHub records creation of [Ho's 4ap repository](https://github.com/boonsuan/4ap); observed initial commit `057d19da7abd21c91b46fe5194c9c32789fa62c8`. |
| September 11, 12:33:11 UTC | Ho's [arXiv v1](https://arxiv.org/abs/2609.12780v1) records submission of the same full negative answer. |
| September 11, 20:38:25.202388 UTC | Conjectures.io records approval of the submission. This is separate from Prize review. |
| September 14, 03:39:34 UTC | The [initial original-repository commit](https://github.com/lkruer/conjectures/commit/8ede860e8fc90a300207a2c17e8aefe6167b3086) contains the identical manuscript and Lean payload. This is a recorded Git date. |
| September 14 | [Public proof claim 311](https://www.erdosproblems.com/forum/thread/196/proof-claims#proof-claim-311) credits both authors; Conjectures.io dates certification/publication to this day. |
| October 8 | Selected proof commit `bf058b903350eb8f873a22ab4a54b2e0faa9727d` preserves the payload and adds the reproducible wrapper and direct corollary. |
| October 10 | [Fresh verification](verification/2026-10-10/report.md) passes source builds, all seven target audits, an independent exact-statement bridge, Lean kernel replay and two Nanoda checks. The separate Discord evidence is authenticated and preserved. |

The Discord message precedes Ho's repository creation by **25 hours, 7 minutes, 23.557 seconds**, and his arXiv submission by **36 hours, 44 minutes, 1.557 seconds**. These are objective differences between the identified provider records. They do not date anyone's unobserved private research.

## Exact manuscript and formal-proof linkage

The Discord-served PDF is 91,799 bytes with SHA-256:

```text
b8b5a37349fcbc3d1fa89842ea67b6798dcb58a256998bb6c5064f3a499a7097
```

It is identical to [the original uploaded manuscript](https://github.com/lkruer/conjectures/blob/8ede860e8fc90a300207a2c17e8aefe6167b3086/problems/erdos-196/paper/proof.pdf) and the PDF at the selected proof commit. Theorem 1.1 states the full negative answer; Sections 2–5 give the finite extension argument; Section 6 constructs the infinite permutation. The independent timestamp therefore attaches to a complete manuscript, not merely a claim to have solved the problem.

The [accepted Lean download](https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73/solution/download) is 26,497 bytes with SHA-256:

```text
e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826
```

It equals the Lean file in the original September 14 upload, the selected preserved payload, and the checked wrapper after removing only its two imports and outer `Bounty` namespace. The [source-identity script](verification/2026-10-10/verify_source_identity.py) and [combined evidence checker](priority-evidence/2026-10-10/verify_priority_evidence.py) verify these relationships. The public Conjectures record dates verification of this payload to 12 minutes before the Discord manuscript was sent. Discord separately corroborates the manuscript's completion, rather than relying solely on the service's database or the PDF's author-controlled date.

The service identifies JenW1N. The manuscript, contemporaneous message and [public author claim](https://www.erdosproblems.com/forum/thread/196/proof-claims#proof-claim-311) support the joint authorship claim; repository ownership alone is not its basis.

## Requested priority findings

1. **Mathematical solution:** Recognize the independently corroborated September 9 completion and transmission of this complete solution, which precedes the identified September 11 competing records. We request priority for this contribution on that basis. September 14 was the public GitHub/forum release, not its earliest documented completion.
2. **Public evidence:** Assess the original private disclosure and the now-public evidence package under the Prize's dated-public-evidence requirement. The September 9 message was not an unrestricted public post. We provide its original link, exact attachment, metadata and reproducible comparisons so the chronology can be independently examined.
3. **Lean formalization:** Apply the Prize's [selected-commit and supporting-history rules](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/docs/award-process.md#lean-formalization-or-both-roles) separately. The selected complete repository version remains the genuine October 8 commit. The service-attested September 9 formal completion is supporting evidence, not a newly asserted September 9 Git commit.

This is an affirmative claim of earlier documented completion among the identified competing records. It does not assert a provider-signed timestamp certificate, rule out unlocated earlier work, establish copying or replace the organizers' attribution and eligibility review. Ho's September 11 public paper remains disclosed. His competing code was not independently compiled in this review.
