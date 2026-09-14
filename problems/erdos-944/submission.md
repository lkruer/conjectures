# Submission — Erdős #944

[Back to the problem](README.md) · [Submission guide](../../docs/submission-guide.md)

**Status: Draft. No announcement has been recorded.**

## Materials

| Item | Record |
| :--- | :--- |
| Official problem | [Erdős #944](https://www.erdosproblems.com/944) |
| Manuscript | [PDF](paper/proof.pdf), September 10, 2026 |
| Authors | Liam Kruer and Jensen Kohlmeyer |
| Lean | [Uploaded sources](lean/) — repository verification pending |
| Proof snapshot for submission | Not frozen; current links above follow the repository branch. |

## Draft summary for author review

**Title:** Vertex-critical four-chromatic graphs with no small critical edge set

**Result:** The manuscript claims a four-color construction and combines it with the higher-color result attributed to Skottova and Steiner. The supplied Lean source targets the existence statement for every k ≥ 4.

**Proof idea:** Punctured cyclic colorings, an integral height character, a winding inequality, and Chinese remainder parameters produce the four-color graphs; a separate higher-color construction completes the existence statement.

**Scope:** This is the existence statement for all k ≥ 4 and r ≥ 1. The manuscript does not assert the stronger statement about every sufficiently large graph order. Its higher-color construction is credited to prior work.

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
