# Erdős 196 publication and attribution record

This submission concerns the complete counterexample in **Erdős 196: A permutation of the natural numbers with no monotone four-term arithmetic progression**, by **Jensen Kohlmeyer ([jenw1n](https://github.com/JENW1N)) and Liam Kruer ([lkruer](https://github.com/lkruer))**. Both are credited for the submitted mathematical construction and Lean formalization. These are contribution credits, not a determination of first discovery or prize entitlement.

## Source and publication history

- **September 9, 2026:** date printed inside the seven-page manuscript. This is an internal manuscript date, not independently established public disclosure.
- **September 11, 2026, 12:33:11 UTC:** arXiv records submission of Boon Suan Ho's [A 4AP-free permutation of the positive integers](https://arxiv.org/abs/2609.12780v1). It states the same full negative answer. This earlier public record is disclosed for mathematical and priority review.
- **September 14, 2026, 03:39:34 UTC:** recorded commit date of this repository's [initial upload](https://github.com/lkruer/conjectures/commit/8ede860e8fc90a300207a2c17e8aefe6167b3086). It includes the [paper](https://github.com/lkruer/conjectures/blob/8ede860e8fc90a300207a2c17e8aefe6167b3086/problems/erdos-196/paper/proof.pdf) and [Lean source](https://github.com/lkruer/conjectures/blob/8ede860e8fc90a300207a2c17e8aefe6167b3086/problems/erdos-196/lean/Erdos196.lean). A commit date alone is not independent proof of first publication time.
- **September 14, 2026, 04:05:27:** timestamp displayed on the [Erdős Problems public proof claim](https://www.erdosproblems.com/forum/thread/196/proof-claims#proof-claim-311), submitted by Liam Kruer and crediting Kruer and Kohlmeyer. The page does not establish correctness or peer review.
- **September 15, 2026:** [Alejandro Zarzuelo's reproduction](https://github.com/alejandrozu/erdos196-counterexample) was linked in the claim discussion. Its report says the unchanged mathematical source compiled with Lean 4.33.1 and a reconstructed wrapper, with standard axioms only. It expressly disclaims independent human peer review. Its separate refinements are not claimed as work by Kohlmeyer or Kruer here.
- **October 8, 2026:** this JSP submission preparation preserved the published paper and mathematical source and recovered the pinned local environment for a fresh check. The new reproduction record specifies exactly what was checked.

No first-publication, independence-from-Ho, established-priority, or award-entitlement claim is made here. JSP maintainers must assess mathematical validity, formal verification, contribution attribution and any competing priority evidence separately.

## Preserved source identities

The PDF supplied again on October 8 is byte-identical to the already published manuscript:

```text
b8b5a37349fcbc3d1fa89842ea67b6798dcb58a256998bb6c5064f3a499a7097  paper/proof.pdf
e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826  lean/Erdos196.lean
5b3c1073ca064c2aa668cfb578aecf3a919e9497c5b2248eee1a30c19bbb1f12  provenance/pasted-2026-10-08.txt
```

The clean `Main (2).lean` file supplied by the author on October 8 is byte-identical to the original published Lean source, with SHA-256 `e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826`.

The earlier October 8 pasted text has corrupted Unicode. The existing public UTF-8 source reproduces that attachment exactly under the documented encoding-corruption transformation. The published source is retained unchanged; the attachment is preserved as evidence, not used as compilable Lean. The reproduction package records the comparison.

## Assistance and review

The manuscript's acknowledgment of extensive OpenAI Codex assistance is preserved. It includes mathematical ideas, proof code, literature checks and manuscript drafting; the named authors are responsible for the submission. October 8 packaging and verification were also performed with Codex. Local compilation and automated inspection do not constitute independent human mathematical peer review or JSP acceptance.

The PDF's historical references to a standalone `Bounty.paper_main`, validator checks and a supplementary archive should be read with the current reproduction report. A fresh build does not retroactively establish every historical check described by the manuscript.
