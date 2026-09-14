# Lean formalization — Erdős #272

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Not uploaded — missing counterpart.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| Not supplied | The PDF references `Solution.lean` and `submission/Main.lean`. | — |

The PDF describes a standalone `Solution.lean` importing `FormalConjectures.ErdosProblems.«272»` and `TaskSupport`, plus `submission/Main.lean` for a task-supplied wrapper. Neither source was included.

## Target and scope

The PDF identifies `Bounty.target` for `Erdos272.erdos_272.variants.szabo_strong`; no source has been received to inspect.

Principal declarations observed in the supplied source: Not inspected: the source file is missing.

The manuscript addresses the Szabó strong variant. It does not claim an exact formula, the optimal linear coefficient, or a classification of every extremal family. Its referenced Lean certificate has not been supplied.

## Reported environment and earlier checks

Section 10 reports Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. These are manuscript-reported versions, not a supplied project.

Section 10 describes compilation, axiom, type, dependency, and static-policy checks for a 12,797-line standalone file. The source and verification record were not included in this upload. See the [manuscript, Section 10](../paper/proof.pdf).

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result | Not run |
| Kernel / axiom audit | Not run |
| Target correspondence | Not independently reviewed |
| File integrity | No Lean file available to compare. |

## Materials still needed for reproduction

Missing primary counterpart: `Solution.lean` or the corresponding `submission/Main.lean`. The PDF also describes `verification.json`, task support, and source TeX that were not supplied.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.

The PDF gives the standalone `Solution.lean` SHA-256 as:

```text
0d651c16942333977ee1ee4ddf17d017e3510f0dc6f2f1dd3542e434d16eb91e
```

This is a manuscript-reported identifier to help locate the missing file, not a checksum verified against an uploaded source.
