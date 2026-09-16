# Lean formalization — Erdős #108

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

[Erdos108.lean](Erdos108.lean) — 1,846 lines. The original filename and file contents are preserved.

The declarations `arc_counterexample_family` and `counterexample_family` construct the stated graph family. `counterexample_of_family` provides the final logical reduction, and `target` asserts `¬ (fcTypeOfName% "Erdos108.erdos_108")`.

## Verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result / kernel audit | Not run |
| Lean and dependency versions | Not supplied |
| Mathematical target correspondence | Not independently reviewed |
| Manuscript coverage | PDF not supplied |
| File integrity | Original contents preserved; checksum in [SHA256SUMS](../SHA256SUMS). |

## Reproduction materials

The source contains no imports and relies on external definitions and the `fcTypeOfName%` macro. Supply the original imports or task wrapper, relevant problem definitions and support, `lean-toolchain`, Lake configuration, dependency manifest, and any previous verification records to establish a reproducible build.
