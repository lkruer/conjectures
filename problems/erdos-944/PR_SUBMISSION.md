# Prepared Justin Sun Prize pull request

This is the exact prepared contribution text. As of 18 October 2026 the submission branch is published, but PR creation was refused by the connected GitHub integration (HTTP 403). A published branch is not a filed PR or an award claim.

## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

This is the original contributors’ registration for **JSP-000785 / Erdős #944**, submitted through coauthor **Liam Kruer’s `lkruer` account**. It records the complete finite-existence solution and its original Lean proof, with **Liam Kruer and Jensen Kohlmeyer (`JENW1N`)** credited separately from later extensions. This is a contribution submission for review, not an award claim or an assertion that verification or an award has been approved.

## Problem

- **Original source:** P. Erdős, *On some Aspects of my Work with Gabriel Dirac*, Annals of Discrete Mathematics 41 (1989), printed page **113**, first paragraph ([original PDF, page 3](https://www.renyi.hu/~p_erdos/1989-19.pdf)); [Erdős Problem #944](https://www.erdosproblems.com/944).
- **Current entry:** [JSP-000785](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000785), currently `Open`, `Lean proof: No`, `Eligible to claim: No`. Proposed change: record the complete solution, original proof source, attribution and publication evidence; mark the solution and Lean proof accepted only after maintainer review. Maintainers determine eligibility and claim-status updates.
- **Related work:** [PR #4668](https://github.com/TheJustinSunPrize/awards/pull/4668) submits peilinliu66-dev’s later prescribed-order extension and finite interfaces, using our original finite-existence proof. This submission registers our own mathematical and Lean contributions; it does not claim that extension or replace its attribution. Our existing evidence appears in [these comments](https://github.com/TheJustinSunPrize/awards/pull/4668#issuecomment-6094259665) and [#5002](https://github.com/TheJustinSunPrize/awards/issues/5002).
- **Complete mathematical solution:** [original manuscript](https://github.com/lkruer/conjectures/blob/8ede860e8fc90a300207a2c17e8aefe6167b3086/problems/erdos-944/paper/proof.pdf), dated **10 September 2026**: Theorem 1.1 establishes the four-colour construction for every edge budget; Corollary 1.2 gives all-colour existence, crediting Skottová–Steiner’s earlier higher-colour result. The statement is existence of a suitable finite graph, not existence at every sufficiently large prescribed order.

## Formal statement

- **Mathematical review status:** submitted for Justin Sun Prize review. [Conjectures.io’s separate record](https://conjectures.io/results/e7afff2c-bb07-4fa8-92b6-67a530aaad70) reports verification on 11 September 2026 and public certification on 16 September. That service’s review is supporting evidence, not Justin Sun Prize approval.
- **Original proof location:** [Solutions/Erdos944.lean](https://github.com/lkruer/conjectures/blob/d42416ace335b42e05c6f46d250c869bce4b5239/problems/erdos-944/lean/reproducible/Solutions/Erdos944.lean).
- **Explicit finite-statement location:** [PrizeSubmission.lean](https://github.com/lkruer/conjectures/blob/d42416ace335b42e05c6f46d250c869bce4b5239/problems/erdos-944/lean/reproducible/PrizeSubmission.lean).
- **Fully qualified final target(s):** `Bounty.target` and `Erdos944Prize.target` (with `Erdos944Prize.benchmark_type_check` checking the original benchmark type).
- **Statement origin:** the `Erdos944.erdos_944` target and `Erdos944.SimpleGraph.IsErdos944` predicate in [frozen Formal Conjectures reference](https://github.com/lkruer/conjectures/blob/d42416ace335b42e05c6f46d250c869bce4b5239/problems/erdos-944/lean/reproducible/FormalConjectures/ErdosProblems/944.lean), preserved from the reported original revision `8432eac998110a563e03df65a28c117e97c8c142`. The submitted statement correspondence remains subject to maintainer review.
- **Coverage:** for every integer `k ≥ 4` and `r ≥ 1`, there is a finite simple graph of chromatic number `k` such that deleting any vertex lowers its chromatic number, while deleting any set of at most `r` distinct unordered edges does not. The construction supplies actual finite cyclic vertex types. The proof covers `k = 4`, `k = 5` and `k ≥ 6`; it does not substitute the narrower `r = 1` Dirac variant for the full problem. The verification report records the final target types and their relation to the original predicate, including finiteness.

## Proof submission

```json
[
  {
    "repository": "https://github.com/lkruer/conjectures",
    "branch": "codex/erdos944-prize-submission",
    "commit": "d42416ace335b42e05c6f46d250c869bce4b5239"
  }
]
```

- **Proof files:** `problems/erdos-944/lean/reproducible/Solutions/Erdos944.lean` (original proof) and `problems/erdos-944/lean/reproducible/PrizeSubmission.lean` (explicit finite statement); final theorem(s) `Bounty.target` and `Erdos944Prize.target` (with `Erdos944Prize.benchmark_type_check` checking the original benchmark type).
- **Provenance and priority evidence:** [SOURCE_HISTORY.md](https://github.com/lkruer/conjectures/blob/d42416ace335b42e05c6f46d250c869bce4b5239/problems/erdos-944/SOURCE_HISTORY.md) identifies the [14 September original repository commit](https://github.com/lkruer/conjectures/commit/8ede860e8fc90a300207a2c17e8aefe6167b3086), the separately accepted Conjectures source, and this reproducible edition. The historical and accepted files have different hashes; they are not represented as byte-identical. The present packaging commit does not backdate itself or replace the earlier evidence. We request review of the documented mathematical and formalization chronology under the normal priority rules.

## Reproduction

- **Compiler:** Lean `4.33.1`; `problems/erdos-944/lean/reproducible/lean-toolchain`.
- **Dependencies:** Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, with the exact remaining dependencies recorded in the submitted `lake-manifest.json` and provenance files.
- **Pinned instructions:** [reproduction README](https://github.com/lkruer/conjectures/blob/d42416ace335b42e05c6f46d250c869bce4b5239/problems/erdos-944/lean/reproducible/README.md).

```sh
git clone --branch codex/erdos944-prize-submission https://github.com/lkruer/conjectures.git
cd conjectures
git checkout d42416ace335b42e05c6f46d250c869bce4b5239
cd problems/erdos-944/lean/reproducible
./verify.sh
```

The script builds `PrizeSubmission` and `AxiomAudit`, then executes the transitive audit again. The report below supplies the actual clean-target build, literal statement inspection and `#print axioms` output for every submitted target. Cached dependency reuse is disclosed; it is not described as a fresh build of Lean or all of Mathlib.

## Pre-submission Lean verification

**PASS — 18 October 2026.** [GitHub Actions run 39160734681](https://github.com/lkruer/conjectures/actions/runs/39160734681) performed the clean build and audit at the selected source commit `d42416ace335b42e05c6f46d250c869bce4b5239`. The [permanent report](https://github.com/lkruer/conjectures/blob/cae4f9f05dab5b0f78afb1f5b16e5ef828e2d397/problems/erdos-944/lean/reproducible/verification/REPORT.md), [machine-readable manifest](https://github.com/lkruer/conjectures/blob/cae4f9f05dab5b0f78afb1f5b16e5ef828e2d397/problems/erdos-944/lean/reproducible/verification/manifest.json), raw logs and source hashes are archived in evidence-only commit `cae4f9f05dab5b0f78afb1f5b16e5ef828e2d397`; that later commit does not change the tested proof.

All **2,339 audited declarations** have no transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The original target, explicit finite target, finite-all-parameters helper, and both benchmark correspondence targets individually report exactly those three standard axioms. The downloaded CI artifact digest and all **204 source checksums** were independently matched to the submitted files. The accepted proof body remains unchanged.

This is a Lean compilation and transitive axiom audit with the official pinned Mathlib cache. It is not an independent second-kernel replay, a full human review of the prose, or a decision on priority or prize eligibility. Reference-file placeholders remain in the archived benchmark but are not dependencies of any submitted final theorem.

## Attribution

- **Original mathematical contribution:** **Liam Kruer (`lkruer`) and Jensen Kohlmeyer (`JENW1N`)**, for the four-colour arbitrary-edge-budget construction and complete finite-existence solution, with the earlier higher-colour mathematics credited below.
- **Original Lean formalization:** **Liam Kruer and Jensen Kohlmeyer**. This is the original coauthor-owned repository; historical sources, the manuscript author list, [Jensen’s public confirmation](https://github.com/TheJustinSunPrize/awards/pull/4668#issuecomment-6094312797), and the source history support the attribution. OpenAI Codex assistance is acknowledged in the manuscript.
- **Prior work:** **Ema Skottová and Raphael Steiner**, for the earlier `k ≥ 5` mathematics ([paper](https://arxiv.org/abs/2508.08703)); **Alex Chan and Kenta Kitamura** retain their earlier restricted `k = 4, r = 1` credits.
- **Later contribution:** **peilinliu66-dev**, for the separately submitted prescribed-order extension, finite interfaces and integration in #4668.
- **Verification:** the external service record and the completed clean CI report are identified separately. No independent human verifier or completed Justin Sun Prize review is claimed.

## Submission checklist

- [x] I changed only the relevant catalog’s solver attribution, Lean proof information or supporting sources and supplied the applicable evidence.
- [x] The submitted result fully solves the original problem. Any submitted Lean proof is complete at the specified commit, with no `sorry`, `admit` or added unproved assumptions replacing proof steps.
- [x] For Lean: I have linked the complete mathematical solution and its proof or publication evidence provided earlier, or supplied them in this PR, and identified the mathematical solver and Lean formalization author separately.
- [x] For Lean: I am claiming my own contribution in the original personal or organization repository, with verifiable contribution evidence; the selected commit is in the named branch, and I supplied statement correspondence, reproduction commands and axiom audit results.
- [x] This PR contains no Lean source files, archives, binaries, vendored dependencies or private identity/contact/payment information.
