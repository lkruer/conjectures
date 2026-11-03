# Erdős #156 — Small maximal integer Sidon sets

[All proofs](../../README.md#proof-index) · [Manuscript](paper/proof.pdf) · [Lean project](lean/) · [Submission record](submission.md)

The manuscript constructs inclusion-maximal Sidon subsets of every sufficiently large integer interval with cardinality O(N^(1/3)), using finite phase colorings, quadratic seeds, periodically labeled anchors, and maximal completion.

| Field | Details |
| :--- | :--- |
| Original problem | [Erdős #156](https://www.erdosproblems.com/156) |
| Justin Sun Prize entry | [JSP-000154](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000154) |
| Authors | Will Howe (@h0w4rd), Grant Huffman (@ghuffy), Jensen Kohlmeyer (@jenw1n), and Liam Kruer (@lkruer) |
| Contribution | Affirmative solution and Lean formalization of the O(N^(1/3)) upper bound |
| Manuscript | [Read the proof](paper/proof.pdf), November 2, 2026, 12 pages |
| Verification | [Recorded checks and scope](lean/verification/report.md) |
| Submission | See [submission record](submission.md) |

## Problem and result

Does there exist a maximal Sidon set A contained in {1,...,N} of size O(N^(1/3))? Maximal means maximal under inclusion in the specified interval; the Sidon property includes diagonal sums 2a.

The manuscript's Theorem 1.1 asserts that there are absolute C > 0 and N0 such that every N >= N0 admits such a set with |A| <= C N^(1/3). Its elementary Proposition 1.2 gives the complementary order-of-magnitude lower bound. The submitted Lean proof concerns the complete upper-bound question, rather than the lower-bound variant or finitely many examples.

## Formalization

The main theorem is `Erdos156.solved`. `IndependentAudit.original_question` separately expands all set and maximality conditions. The [build record](lean/README.md) identifies the fixed toolchain, dependency manifest, original files, portable wrapper, and verification commands.

## Attribution and assistance

The submitting author reports joint mathematical and Lean contributions by all four named authors. The manuscript acknowledges substantial OpenAI Codex assistance. Submission records and formal checking do not replace the prize committee's review or each contributor's own identity and award-claim process.

## Prior work

- P. Erdős, A. Sárközy, and V. T. Sós, *On sum sets of Sidon sets, I*, Journal of Number Theory 47 (1994), 329–347.
- I. Z. Ruzsa, *A small maximal Sidon set*, Ramanujan Journal 2 (1998), 55–58; earlier upper bound O((N log N)^(1/3)).

## Revision notes

- November 2, 2026: supplied manuscript and both source formats preserved; standalone project and explicit statement bridge prepared for prize review.
