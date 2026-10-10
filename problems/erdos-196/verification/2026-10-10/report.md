# Erdős 196 submission verification and priority review

**Overall verdict: Verification passed for the specified Lean proof. Prize acceptance and priority remain undecided.**

The complete disproof at `lkruer/conjectures`, commit `bf058b903350eb8f873a22ab4a54b2e0faa9727d`, addresses the original four-term progression question. A fresh source build, exact statement checks, axiom checks, Lean kernel replay and an independent Nanoda check passed. This is a technical verification by an AI assistant, not the Prize committee's mathematical review or an independent human referee report.

| Required question | Judgment | Decisive evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | Yes | It constructs a bijection of all natural numbers with no four values in arithmetic progression at any increasing indices. Both value orientations are covered. |
| Did the specified commit actually pass verification? | Yes | The submitted sources were unchanged; all final target checks, source builds and checker commands exited 0. See [execution record](result.json). |
| Does it fully solve the original problem? | Yes, as a complete formal disproof within the stated trust scope | The finite extension, exhaustion of all naturals, injectivity, surjectivity and unrestricted avoidance are proved. |
| Does it meet the Lean completeness requirements for this verification? | Meets | Every required target and the independent bridge passed, using only standard Lean axioms. |

## Source and submission

The [existing Prize PR 4875](https://github.com/TheJustinSunPrize/awards/pull/4875) concerns **JSP-000185**, which is **Erdős 196**. The audit used the PR's specified [original repository commit](https://github.com/lkruer/conjectures/tree/bf058b903350eb8f873a22ab4a54b2e0faa9727d/problems/erdos-196/lean/reproduction), on `jsp-000185-erdos196`. It did not substitute another contributor's implementation.

The awards base was `16877004910734cecca83cc5af0fec2f5a4125b3`; the inspected PR head was `31ae73746215f6e1e02a0d579f3bde6fa97f45a8`. The PR was open and unmerged, with no posted review or comment at inspection. The inspection preceded this evidence update; the proof sources were not changed during verification or evidence publication.

The original mathematical question is available at [Erdős Problems](https://www.erdosproblems.com/196) and in the introduction of [Ho's paper, version 1](https://arxiv.org/html/2609.12780v1). The submitted seven-page manuscript states the full counterexample in Theorem 1.1, proves finite extension in Sections 2–5 and constructs the infinite permutation in Section 6. Its prose and the formal source were inspected separately; compilation alone does not certify the exposition.

## Statement and coverage

The submitted target is

```lean
Bounty.target : ¬ (True ↔ ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4)
```

The independently authored [bridge](Independent196.lean) checks the direct statement

```lean
∃ p : ℕ ≃ ℕ, ∀ a b c d : ℕ,
  a < b → b < c → c < d →
  ¬ (p a + p c = 2 * p b ∧ p b + p d = 2 * p c)
```

| Original obligation | Formal evidence | Coverage |
| --- | --- | --- |
| Permute every natural number exactly once | `permFun_injective`, `permFun_surjective`, `Equiv.ofBijective` | Full |
| Avoid four-term progressions at arbitrary increasing indices | `permFun_no_four`, `paper_main`, `checked196` | Full |
| Cover increasing and decreasing values | The two arithmetic equations impose no sign restriction on the common difference | Full |
| No unproved extension premise | `finite_extension` supplies the next finite stage; nested stages exhaust all naturals | Full |
| Refute the actual original universal statement | `counterexample` and `target`, checked against the pinned challenge type | Full |

Injectivity excludes zero common difference. Translating both indices and values by one converts a permutation of zero-based naturals to one of positive integers and preserves the two arithmetic equations. The result is not restricted to adjacent entries, equally spaced indices, odd differences, a finite initial segment or a subset of the naturals.

## Verification and trust scope

The check followed the [Prize's Lean verification skill](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/skills/lean-verify/SKILL.md). Its [preflight](preflight/result.json) and [postflight](postflight/result.json) both passed without issues at the same proof commit. The seven-target manifest is [targets.json](targets.json).

The macOS ARM64 run used Lean **4.33.1**, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The submitted bootstrap reconstructed Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142` from the recorded official base and patch; its problem 196 source is unchanged. Standard dependency caches were reused at their pinned revisions. The Formal Conjectures utility objects, task statement, support, submitted proof and direct corollary were freshly built.

The restricted environment denied network access and writes outside the fresh project and audit directories. The control test denied reading and writing an unrelated file and denied a network connection. See [sandbox profile](sandbox.sb), [environment](environment.json) and [self-test log](logs/sandbox-self-test.log). Host runtime libraries and the selected toolchain remained trusted. This was not a clean rebuild of all Mathlib sources.

| Check | Observed result |
| --- | --- |
| Fresh source build | Utilities, original statement, `Erdos196.lean` and `PaperMain.lean` exited 0 |
| Original audit and independent bridge | Exited 0 with `--trust=0` |
| All seven target types, bodies and axioms | Passed; see [detailed output](logs/detailed-targets.log) |
| Lean kernel replay | `leanchecker --verbose Erdos196 PaperMain`, exit 0; [log](logs/kernel-replay.log) |
| Independent exporter | Official `lean4export` at `15f6055e299ad5b89345e533cc2192f4cc00f659`, built with the matching 4.33.1 compiler; export exited 0 |
| Independent Nanoda checker | Version 0.4.17 and separately source-built 0.4.19 both exited 0, **7,300 declarations checked with no errors**; [latest log](logs/nanoda-0.4.19.log) |
| Source stability | All audited submitted source hashes remained unchanged; [hashes](source-hashes.json) |

For each of `Bounty.target`, `Bounty.paper_main`, `Bounty.Construction196.counterexample`, `Bounty.Construction196.finite_extension`, `Bounty.Construction196.permFun_injective`, `Bounty.Construction196.permFun_surjective` and `Bounty.Construction196.permFun_no_four`, the complete reported axiom set was:

```text
[propext, Classical.choice, Quot.sound]
```

The same set was reported for `checked196`. No `sorryAx`, native-computation trust axiom or unproved extension axiom enters these proofs. The original imported challenge has an admitted theorem body; the submission obtains its type and proves its negation independently. That admitted body is absent from the audited proof dependencies.

The generic audit runner's build route would not preserve this task's `google.answer=always_true` statement setup, so explicit matching build and target commands were used. Their exact arguments, working directory, durations and results are in [result.json](result.json), with drivers and raw logs alongside it. An initial attempt to emit the independent bridge object used the wrong filesystem root and failed before compilation. Only the audit invocation's `--root` was corrected; no submitted source changed. Both attempts remain recorded.

The additional Nanoda 0.4.19 check used unmodified source at [`ammkrn/nanoda_lib` commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7), built offline in a restricted environment after fetching locked dependencies. Its binary hash and invocation are in [nanoda-latest-result.json](nanoda-latest-result.json); the [source build record](checker-build/result.json) is retained.

The 28,198,472-byte independent export was retained locally; its uncompressed SHA-256 `3a4c867bd23b1bdb1e42f3411b0d3b41825411c4beabdcffa9e4bb9c154c846c` and exact export command are in [the execution record](result.json). It is regenerated from the pinned source and is not duplicated in this publication. Nanoda allowed exactly the three standard axioms and had `unsafe_permit_all_axioms=false`. This checks the exported proof closure independently of Lean's kernel; it does not establish priority or author identity.

## Priority evidence

**October 10 evidence update: the complete submitted manuscript is independently corroborated on Discord on September 9 at 23:49:09 UTC.** The original message, its attachment ID and CDN Last-Modified agree. The downloaded 91,799-byte PDF is identical to the manuscript in the original September 14 upload and selected proof commit, with SHA-256 `b8b5a37349fcbc3d1fa89842ea67b6798dcb58a256998bb6c5064f3a499a7097`. See the [evidence report, receipt and screenshot](../../priority-evidence/2026-10-10/README.md) and [passing combined checks](../../priority-evidence/2026-10-10/checks.json).

The [Conjectures.io public result](https://conjectures.io/v1/results/e73b95f7-1d1b-42b5-a442-c07077741d73) records verification at **September 9, 23:36:51.116698 UTC**, isolated replay September 10, approval September 11 and certification/publication September 14. Its accepted Lean source, SHA-256 `e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826`, is identical to the original upload and the selected payload; the documented import/namespace-only wrapper preserves the proof. This connects the historical service record to the checked formalization. Discord supplies separate corroboration of the complete mathematical manuscript's existence and transmission.

The sending message predates creation of [Ho's repository](https://github.com/boonsuan/4ap), September 11 at 00:56:33 UTC, by **25 hours, 7 minutes, 23.557 seconds**. It predates [Ho's arXiv v1](https://arxiv.org/abs/2609.12780v1), September 11 at 12:33:11 UTC, by **36 hours, 44 minutes, 1.557 seconds**. These are objective comparisons of identified records, not dates for anyone's private discovery. Ho's code was not independently compiled in this review.

**The authors claim priority for the complete mathematical solution on the basis of the documented September 9 completion.** This new evidence strengthens that claim beyond the previous retrospective service record and internal PDF date. The original Discord post is a private direct message, so it does not establish unrestricted public publication on September 9. The Prize's public-evidence requirement and the genuine October 8 selected-commit anchor for formalization remain for organizer review. The [priority statement](../../PRIORITY.md) distinguishes those findings explicitly.

The bounded literature check distinguished earlier partial results: Geneson's August 2026 paper separates its density results from full enumeration; the classical three-term obstruction and five-term avoidance results do not settle the four-term question; restricted-difference results do not imply this unrestricted theorem. See the existing PR's linked literature and [earlier evidence manifest](priority-evidence.json).

## Submission status

The current PR already supplies the original repository, full pinned commit, complete manuscript, precise negative target, reproduction instructions, all seven axiom checks, author credits and the service and Ho chronology. No confirmed submission-format defect was found. This publication adds the complete verification evidence and an executable source-identity check. It preserves the original proof commit and submits the September 9 completion evidence for separate mathematical and Lean priority review.

The remaining requirements are organizer review of the mathematics, formalization, attribution and priority; acceptance/merge; the applicable public review period; and each contributor's own claim and identity process. These cannot be completed by changing a local proof file. In particular, neither the earlier service payment nor this successful verification makes the unmerged Prize submission eligible for payment automatically.


## Reproduce the source-identity check

Run `python3 problems/erdos-196/verification/2026-10-10/verify_source_identity.py` from the repository checkout. The script verifies the recorded service download against the original September 14 Git object and preserved payload, checks the selected proof-source hashes, and removes only the documented imports/outer namespace to recover the identical payload. It verifies the source linkage, not the historical date or authenticity of the service's record. [Identity result](source-identity-result.json) and [priority statement](../../PRIORITY.md).
