# Erdős #944

**Vertex-critical four-chromatic graphs with no small critical edge set**

Liam Kruer and Jensen Kohlmeyer · September 10, 2026

[Read the proof](paper/proof.pdf) · [Reproducible Lean package](lean/reproducible/) · [Source history](SOURCE_HISTORY.md) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #944](https://www.erdosproblems.com/944) |
| Contribution | Four-color construction for arbitrary edge robustness; all-color existence with earlier higher-color work credited. |
| Manuscript | [PDF, 13 pages](paper/proof.pdf) |
| Manuscript date | September 10, 2026 |
| Manuscript review | External mathematical review remains required; local checks establish formal scope and reproduction only. |
| Lean | Exact accepted source and pinned reproduction package available; see verification record. |
| Submission | Original-author submission prepared for JSP-000785; see submission notes. |

## Problem and manuscript claim

For every $k\geq4$ and $r\geq1$, does there exist a finite $k$-chromatic vertex-critical graph whose chromatic number remains $k$ after deleting any set of at most $r$ edges?

The manuscript gives a four-color construction and combines it with the higher-color result of Ema Skottová and Raphael Steiner. The accompanying Lean source targets existence for every k ≥ 4. The original mathematical and formalization authors are **Liam Kruer (`lkruer`) and Jensen Kohlmeyer (`JENW1N`)**, with the manuscript’s OpenAI Codex assistance disclosure retained.

The Conjectures.io record reports verification and certification of the full existence result. The Justin Sun Prize organizers must review correctness, attribution, priority, eligibility, and any award. See [source history](SOURCE_HISTORY.md) for the separate evidence and dates.

## Scope and reading guide

This is the existence statement for all k ≥ 4 and r ≥ 1. The manuscript does not assert the stronger statement about every sufficiently large graph order. Its higher-color construction is credited to prior work.

Theorem 1.1 states the four-color construction and Corollary 1.2 gives all-color existence. Sections 2–7 develop the construction; Section 8 covers the formalization, prior higher-color result, and reported checks.

## Formalization

`Bounty.target` for `Erdos944.erdos_944`.

See the [Lean record](lean/README.md) and [reproduction package](lean/reproducible/) for the exact accepted body, pinned environment, and verification evidence. The historical September standalone source is preserved unchanged. It is not byte-identical to the accepted source; the manuscript’s historical check claims are distinguished from current checks.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. The historical upload did not independently reassess prior literature.

## Revision notes

- **Historical upload note:** Earlier versions recorded 2026-09-13. The introducing Git commit is dated **2026-09-14 03:39:34 UTC**. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.

- **2026-10-18:** Added the exact accepted source’s reproduction environment, explicit statement checks, and original-author submission evidence. This packaging date does not replace the original public chronology.
