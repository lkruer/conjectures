# Submission — Erdős #14

[Back to the problem](README.md) · [Submission guide](../../docs/submission-guide.md)

**Status: Draft. No announcement has been recorded.**

## Materials

| Item | Record |
| :--- | :--- |
| Official problem | [Erdős #14](https://www.erdosproblems.com/14) |
| Manuscript | [PDF](paper/proof.pdf), September 13, 2026 |
| Authors | Liam Kruer and Jensen Kohlmeyer |
| Lean | [Uploaded sources](lean/) — repository verification pending |
| Proof snapshot for submission | Not frozen; current links above follow the repository branch. |

## Draft summary for author review

**Title:** A uniform square-root lower bound for non-unique sums and a resolution of Erdős problem 14

**Result:** The manuscript claims the uniform bound $\sqrt{N}<12000 E_A(N)$ for every $A$ and every integer $N\geq 2\cdot 10^{24}$. It uses this to answer part I affirmatively and part II negatively.

**Proof idea:** The shared finite estimate combines a triple-sum moment identity, counting pairs in an arithmetic progression, and incompatible estimates for a finite generating polynomial.

**Scope:** Both parts are covered by the unified PDF. The two supplied Lean files have separate final targets and duplicate the shared core; they should be checked separately in their respective task wrappers.

**Formalization:** The accompanying sources are available in the repository. The manuscript describes prior checks; this repository has not reproduced them yet.

**Assistance disclosure:** The manuscript credits substantial assistance from OpenAI Codex in proof development, Lean formalization, and manuscript preparation. Preserve the manuscript’s specific acknowledgments in any announcement.

## Before posting

- [x] The supplied PDF and its title, authors, and date are recorded.
- [x] The availability of the supplied Lean files is accurately recorded.
- [ ] Recheck the current problem statement and relevant literature.
- [ ] Complete author review of the argument and any remaining gaps.
- [ ] Confirm the precise scope and evidence behind any verification claims.
- [ ] Freeze the version to share and replace the current links with commit permalinks.
- [ ] Check the current site guidance and approve the final announcement text.

## Submission and follow-up history

No submissions or site references recorded. Add the date, destination or comment permalink, and proof revision after an actual announcement.
