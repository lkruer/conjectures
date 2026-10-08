# Lean formalization — Erdős 196

[Back to the problem](../README.md) · [Reproduction package](reproduction/README.md)

**Status: Build passing; scope recorded.** Local verification on October 8, 2026 compiled the original construction in Lean 4.33.1 with the original Formal Conjectures pin. Mathematical review and JSP acceptance remain pending.

## Sources and theorem

[Erdos196.lean](Erdos196.lean) is the unchanged 635-line original submission body. Its SHA-256 is `e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826`. The [complete wrapped source](reproduction/Erdos196.lean), task support, locked environment and commands are supplied in the reproduction package.

The main theorem is `Bounty.Construction196.counterexample : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP f 4`. The exact task theorem `Bounty.target` negates `True ↔ ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4`. Both the increasing and decreasing four-term progression cases are covered. The construction is a bijection of all naturals, not just a permutation of a subset.

## Verification and trust

The main theorem, its four-term-avoidance lemma and the final target each have only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies. The admitted open conjecture in the imported catalogue is not a dependency of these results. See the package's recorded commands, full audit and precise verification limits.

The original pinned environment is Lean 4.33.1 and Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`. That revision is a deterministic validator patch on a public upstream commit. The bootstrap script reconstructs and verifies its exact tree and commit. No mathematical proof edit was required; the corrupted October 8 pasted text is preserved separately and compared with the clean public payload.

## Manuscript correspondence

The manuscript's Section 7 describes historical validator checks, a standalone `Bounty.paper_main`, and a supplementary archive. Those assertions are not replaced by claims about an unperformed historical replay. The current reproduction supplies its own freshly checked index corollary and explicitly reports the checks run on October 8. It does not establish independent human peer review.

[Publication and attribution history](../PUBLICATION-HISTORY.md) distinguishes the manuscript date, public proof claim, prior literature and third-party reproduction.
