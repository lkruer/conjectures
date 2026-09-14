# Submission — Erdős #196

[Back to the problem](README.md) · [Submission guide](../../docs/submission-guide.md)

**Status: Draft. No announcement has been recorded.**

## Materials

| Item | Record |
| :--- | :--- |
| Official problem | [Erdős #196](https://www.erdosproblems.com/196) |
| Manuscript | [PDF](paper/proof.pdf), September 9, 2026 |
| Authors | Jensen Kohlmeyer and Liam Kruer |
| Lean | [Uploaded sources](lean/) — repository verification pending |
| Proof snapshot for submission | Not frozen; current links above follow the repository branch. |

## Draft summary for author review

**Title:** Erdős 196: A permutation of the natural numbers with no monotone four-term arithmetic progression

**Result:** The manuscript claims a bijection $p:\mathbb{N}_0\to\mathbb{N}_0$ with no indices $i<j<k<\ell$ satisfying both $p(i)+p(k)=2p(j)$ and $p(j)+p(\ell)=2p(k)$.

**Proof idea:** Finite prefixes are extended using binary residue orders and a finite saturation argument, preserving compatibility conditions until every natural number has been included.

**Scope:** The claimed permutation enumerates all natural numbers and avoids both directions of monotone four-term progressions. The supplied Lean file is the body intended for the counterexample task wrapper.

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
