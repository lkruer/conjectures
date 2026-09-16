# Erdős #108

**A counterexample to Erdős problem 108**

[Lean source](lean/Erdos108.lean) · [Verification record](lean/) · [Manuscript record](paper/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Problem page | [Erdős #108](https://www.erdosproblems.com/108) |
| Contribution | Counterexample (source claim). |
| Manuscript | Not uploaded |
| Authors and manuscript date | Not specified in the supplied source |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Result and scope

The source constructs graphs with arbitrarily large chromatic number whose subgraphs of girth at least five are six-colorable. Its final reduction uses girth five and chromatic number seven to target the negation of `Erdos108.erdos_108`.

This description follows the supplied Lean file. Compilation and correspondence to the intended problem statement have not been independently checked in this repository.

## Formalization

The uploaded [Erdos108.lean](lean/Erdos108.lean) contains 1,846 lines and ends with:

```lean
theorem target : ¬ (fcTypeOfName% "Erdos108.erdos_108") := by
  exact counterexample_of_family counterexample_family
```

The file contains no imports; the original imports or task wrapper and pinned project are needed to reproduce a build. See the [verification record](lean/README.md).

## Revision notes

- **2026-09-15:** Added the supplied Lean source unchanged. The PDF remains to be supplied. [SHA256SUMS](SHA256SUMS) records the original file checksum.
