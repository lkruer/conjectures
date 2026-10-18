# Original-author submission — Erdős #944 / JSP-000785

[Problem](README.md) · [Manuscript](paper/proof.pdf) · [Reproduction package](lean/reproducible/) · [Source history](SOURCE_HISTORY.md)

The original mathematical and Lean contributions are credited to **Liam Kruer (`lkruer`) and Jensen Kohlmeyer (`JENW1N`)**. This package is prepared from the original author-controlled repository for review by the Justin Sun Prize. Preparation, submission, and even a successful proof check do not announce an award.

## Contribution submitted

For every `k ≥ 4` and `r ≥ 1`, there exists a finite `k`-vertex-critical graph whose chromatic number cannot be lowered by removing at most `r` unordered edges. The new mathematical contribution is the four-color construction for arbitrary `r`. The earlier higher-color mathematics is credited to **Ema Skottová and Raphael Steiner**, and the Lean source covers every required color count.

The historical manuscript has Theorem 1.1 for four colors and Corollary 1.2 for all colors. Its OpenAI Codex assistance disclosure is retained. Earlier `r=1` work by Alex Chan and Kenta Kitamura retains its credit. The submitted existence theorem does not claim peilinliu66-dev’s later prescribed-order extension.

## Evidence and verification

- The exact manuscript is also published at [jenwin.io](https://jenwin.io/papers/erdos-944.pdf).
- [Source history](SOURCE_HISTORY.md) identifies the manuscript, original September repository snapshot, accepted proof body, and coauthor’s later reproducible edition without conflating their dates or hashes.
- The [reproduction package](lean/reproducible/) supplies pinned Lean/Mathlib dependencies, the accepted body, an explicit finite-existence theorem, integrity checks, and a transitive axiom audit. Only the recorded successful run establishes a completed check; a pending workflow is not a verification result.
- The [separate Conjectures.io result](https://conjectures.io/results/e7afff2c-bb07-4fa8-92b6-67a530aaad70) records acceptance on 11 September and public certification on 16 September 2026. Its award does not establish Justin Sun Prize eligibility or payment.

## Related Justin Sun Prize records

[PR #4668](https://github.com/TheJustinSunPrize/awards/pull/4668) contains the later prescribed-order extension and integration. The original coauthors already supplied [chronology evidence](https://github.com/TheJustinSunPrize/awards/pull/4668#issuecomment-6094259665) and [original-source evidence](https://github.com/TheJustinSunPrize/awards/pull/4668#issuecomment-6094312797). [Issue #5002](https://github.com/TheJustinSunPrize/awards/issues/5002) asks for review and is not an award claim.

The original-author contribution submission is distinct: it registers the original complete existence proof and original formalization from `lkruer`, with Jensen’s coauthorship retained. It requests separate review of each contribution’s provenance and scope. It does not seek credit for the later prescribed-order extension or erase prior work.

## Remaining organizer and author steps

The organizers must review the mathematics, reproduce the proof, reconcile attribution and priority, and accept the contribution before a normal legacy award claim can proceed. Each actual claimant then submits their own claim and completes personal identity verification and written confirmation. No proxy claim, payment instructions, or private identity material is included here. The organizers publish the candidate and start the applicable 14-day review; no clock is claimed to have started merely from this repository or submission.
