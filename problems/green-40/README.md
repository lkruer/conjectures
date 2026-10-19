# Green #40 — f(2)

**Asymptotically optimal binary linear covering codes of radius two**

Jensen Kohlmeyer and Liam Kruer · September 15, 2026

[Read the proof](paper/proof.pdf) · [Lean source record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Collection | [Ben Green, *100 open problems*](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), Problem 40 |
| Contribution | The radius-two equality f(2) = 1 (manuscript claim). |
| Manuscript | [PDF, 8 pages](paper/proof.pdf) |
| Manuscript date | September 15, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Accepted submission body recovered; not checked locally |
| Submission | [External certificate recorded](submission.md) |

## Result and scope

The manuscript claims a sequence of binary linear codes with covering radius at most two, lengths tending to infinity, and covering densities tending to one. Together with the sphere-covering lower bound, this yields $f(2)=1$.

The result addresses the radius-two question identified in the discussion of Green’s Problem 40. It does not settle the general question of the growth of $f(r)$ as the covering radius increases.

Theorem 1.1 states the construction and equality. Sections 3–7 develop the quadratic maps, graph repair, parity-check codes, and density limit; Section 8 describes the Lean formalization.

## Formalization

The PDF names `Green40.lean` as a single-file proof with `Bounty.target`, whose stated type resolves to `True ↔ Green40.f 2 = 1`. The [accepted submission body](lean/Main.lean) was recovered byte for byte from Conjectures.io on 2026-10-18, preserving the download's filename `Main.lean`. It relies on the task's imports and enclosing namespace. See the [Lean record](lean/README.md) for its provenance, external certificate, and missing local reproduction materials.

## References and acknowledgments

The [original PDF](paper/proof.pdf) preserves the authors’ references and credits. It acknowledges OpenAI ChatGPT/Codex assistance, the Formal Conjectures and mathlib contributors, and the public Conjectures.io contribution used for the formal sphere-covering lower bound.

## Revision notes

- **2026-09-15:** Added the supplied PDF unchanged; the Lean counterpart remains to be supplied. See the [manuscript record](paper/README.md), [SHA256SUMS](SHA256SUMS), and [upload inventory](../../docs/upload-inventory.md).
- **2026-10-18:** Recovered the accepted Conjectures.io submission body as `lean/Main.lean` without changing its bytes. Recorded its certificate and checksum; no local Lean build was performed. The historical PDF is unchanged.
