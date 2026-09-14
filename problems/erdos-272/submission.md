# Submission — Erdős #272

[Back to the problem](README.md) · [Submission guide](../../docs/submission-guide.md)

**Status: Draft. No announcement has been recorded.**

## Materials

| Item | Record |
| :--- | :--- |
| Official problem | [Erdős #272](https://www.erdosproblems.com/272) |
| Manuscript | [PDF](paper/proof.pdf), September 9, 2026 |
| Authors | Jensen Kohlmeyer and Liam Kruer |
| Lean | **Missing** — PDF references `Solution.lean` |
| Proof snapshot for submission | Not frozen; current links above follow the repository branch. |

## Draft summary for author review

**Title:** A linear error bound for Erdős problem 272

**Result:** The manuscript claims $\binom{N}{2}+1\leq t(N)\leq N^2/2+30000N$ for all sufficiently large $N$, yielding the linear error term.

**Proof idea:** A structural reduction removes a linear number of exceptional members; primitive-pair assignments and private witnesses then control the remaining family with a linear error.

**Scope:** The manuscript addresses the Szabó strong variant. It does not claim an exact formula, the optimal linear coefficient, or a classification of every extremal family. Its referenced Lean certificate has not been supplied.

**Formalization:** The manuscript describes a Lean certificate, but the source has not yet been uploaded.

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
