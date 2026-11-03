# Verification passed — Erdős 156 / JSP-000154

The portable project fully proves the original eventual O(N^(1/3)) upper-bound question with the standard Sidon definition, including diagonal sums, and inclusion maximality inside {1,...,N}. It is ready to submit for the prize committee's mathematical and formal review. This is a verification report, not an award or priority determination.

| Required judgment | Conclusion | Evidence |
| --- | --- | --- |
| Does the proof address the original problem? | Yes | The explicit bridge `IndependentAudit.original_question` spells out containment, Sidonicity, maximality, and one uniform constant for all sufficiently large N. |
| Did the checked version pass? | Yes, this content-hashed portable project | Source check, explicit bridge, all-theorem axiom audit, and kernel replay exit 0. The publication commit is recorded in the submission record. |
| Does it fully solve the original question? | Yes, within the stated standard classical Lean foundations | No additional hypotheses appear in the main theorem; the complete asymptotic upper bound is established. |
| Does it meet Lean completeness requirements? | Meets | No placeholders or new axioms occur in the proof's dependency chain. |

## Inputs and exact scope

Review date: November 2, 2026 (America/New_York).

- Original problem: [Erdős #156](https://www.erdosproblems.com/156), with [source text](https://www.erdosproblems.com/latex/156).
- Prize mapping: [JSP-000154](https://github.com/TheJustinSunPrize/awards/blob/89cf2ffd9d2158e57437e2f37aca4b3d3af32cc3/problems/catalog-0101-0200.md#JSP-000154). JSP numbers and Erdős numbers differ.
- Supplied manuscript: *Small Maximal Integer Sidon Sets by Finite Phase Colorings*, November 2, 2026, 12 pages. Theorem 1.1 is the target; Proposition 1.2 is supporting lower-bound context.
- Supplied upload payload: SHA-256 `ff5a14b368a5e46931808a48883ae0a4ec4546d032c3c4576818a45399b8bdb2`.
- Complete companion named in the manuscript: SHA-256 `e266058ad3e0e487ea88440470c6d8dbc0f51999b08daa68c0fce5bd3bdc664b`, which matches the manuscript's recorded digest.
- PDF SHA-256: `b291a37dddf2f8d30adf0362574ab2e00bef2bbc551b2cdabef0df89f2c7e716`.

Both original Lean formats and the manuscript are preserved. The original challenge bundle at the paper's `bf40872fe09f3c9c94e5b1480823a0622cc1698a` reference was not reproduced. Instead, this report checks the separately identified portable package. Its only changes inside the upload body are the two explicit expansions of the target-type macro; the enclosing namespace, import, and exponentiation setting are supplied in the wrapper. Source preservation is checked mechanically. See [source hashes](source-hashes.json).

An initial harness used a named target alias that Lean's rewrite tactic did not unfold. The final harness expands the target literally, matching the original macro's effect. Those initial harness failures are retained in the logs and are not mathematical proof failures. No proof step was repaired or replaced.

## Statement correspondence

| Original requirement | Formal declaration or definition | Assessment |
| --- | --- | --- |
| Finite integer set contained in {1,...,N} | `Set.IsMaximalSidonSetIn`, expanded in `IndependentAudit.original_question` | Exact containment, with endpoints included. |
| Unique unordered pair sums, including repeated elements | `IsSidon` and the four universally quantified marks in the explicit bridge | No distinctness restriction; diagonal sums included. |
| Inclusion maximality within the host interval | Every omitted x in {1,...,N} destroys the Sidon property on insertion | Exact intended maximality, rather than maximum cardinality. |
| A single O(N^(1/3)) constant for all sufficiently large N | `Bounty.Construction.eventual_small_maximal_sets` and the explicit bridge | Constant chosen before the `atTop` quantifier; no finite-size restriction. |
| Standard minimum-cardinality formulation | `Bounty.target_iff_small_maximal_sets`, `Erdos156.solved` | Minimum is attained and equivalent to the construction statement. |

The locally stated definitions match the [public Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/156.lean) and its supporting definitions at that revision. No unproved conjecture is imported or assumed by this portable project.

## Execution and trust

Exact toolchain: official Lean 4.35.0-rc2, Linux x86_64. Its release archive matches the publisher's SHA-256 `b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049`.

Mathlib is pinned at `065356127b1dc0016f66b7283ce0ce2c4055aa55`; all eight transitive dependency revisions were checked against the included lockfile. Official cached library artifacts were used. Submitted sources were recompiled.

Execution ran in a Bubblewrap namespace sandbox inside Ubuntu/WSL, with a cleared environment, no credentials or home-directory access, and networking disabled for proof checking. Only the dedicated project, toolchain, system runtime, and cache were visible. Network access was enabled separately for dependency cache download. Commands had recorded time limits; source checks used a 16000 MB Lean limit.

| Check | Exit | Time | Evidence |
| --- | --- | --- | --- |
| `build-main` | 0 | 48.63 s | [log](logs/build-main.log) |
| `source-check` | 0 | 35.58 s | [log](logs/source-check.log) |
| `audit` | 0 | 5.33 s | [log](logs/audit.log) |
| `all-axioms` | 0 | 5.58 s | [log](logs/all-axioms.log) |
| `kernel-replay` | 0 | 29.31 s | [log](logs/kernel-replay.log) |

Verification levels completed: static statement/source review; actual Lean source checking; explicit statement bridge; and kernel replay of `Statement`, `Erdos156`, and `Main`. Replay starts from the trusted imported libraries. A full fresh replay of all of mathlib and an independently implemented external checker were not run. No claim of those additional verification levels is made.

`Bounty.target`, `Erdos156.solved`, the reformulation bridge, the final construction, and the independently expanded statement all report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

All 178 public theorem declarations were audited; every reported axiom set is a subset of these standard foundations. There is no `sorryAx`, native-computation axiom, or additional unproved assumption. See [all axioms](logs/all-axioms.log) and the [explicit bridge output](logs/audit.log). The direct source check has zero errors and zero warnings.

## Manuscript and submission notes

The 12 pages were inspected, including the complete extracted text and rendered layout, with detailed inspection of the opening theorem and verification appendix. The construction, quantifier order, and Lean correspondence were reviewed. No mathematical gap or scope mismatch was identified in this review.

The manuscript says 167 public theorems, omitting 11 declarations with inline simplifier attributes from that count; there are 178 public declarations. The fresh audit includes all 178. This correction is recorded in the accompanying paper notes without altering the supplied PDF.

The authors are Will Howe (@h0w4rd), Grant Huffman (@ghuffy), Jensen Kohlmeyer (@jenw1n), and Liam Kruer (@lkruer). Joint contributions to mathematics and formalization were confirmed by the submitting user. Individual identities, priority, prize eligibility, and any eventual award remain matters for the prize process. No external human peer-review acceptance is claimed.

The correct initial prize action is a catalog-reference PR for JSP-000154. The proof and manuscript belong in the authors' separate repository. Each contributor's later award claim must be initiated through their own account under the [official process](https://www.hejustinsun.com/prize/participation).
