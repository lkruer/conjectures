# Upload inventory

[Back to the proof index](../README.md#proof-index)

The September 13, 2026 upload contains **six PDFs and six Lean source files for six problem numbers**. Every problem has a PDF. **#272 is the only problem missing a primary Lean counterpart.**

| Problem | Original PDF filename | Pages | Original Lean filename(s) |
| :--- | :--- | ---: | :--- |
| [#14](../problems/erdos-14/) | `Erdos14_Unified_Paper.pdf` | 8 | `Erdos14_PartI.lean`, `Erdos14_PartII_Counterexample.lean` |
| [#96](../problems/erdos-96/) | `erdos96-convex-unit-distances.pdf` | 8 | `erdos96.lean` |
| [#196](../problems/erdos-196/) | `Erdos196-Kohlmeyer-Kruer (1).pdf` | 7 | `Erdos196.lean` |
| [#272](../problems/erdos-272/) | `erdos272-linear-error (1).pdf` | 15 | **Missing** |
| [#354](../problems/erdos-354/) | `erdos354-Kohlmeyer-Kruer.pdf` | 13 | `lean354` |
| [#944](../problems/erdos-944/) | `erdos944-kruer-kohlmeyer (2).pdf` | 13 | `erdos944.lean` |

## File handling and scope

- PDFs are stored as `paper/proof.pdf` in each problem folder. PDF and Lean contents were copied byte for byte; each folder contains a `SHA256SUMS` record.
- The extensionless Lean file `lean354` is stored as `Erdos354.lean`. All other Lean filenames are retained.
- The #14 unified PDF and its two Lean files cover both parts, so a second PDF is not needed for this upload.
- The #354 pair covers part I (multiplier 2). No claim is made here about the separate multiplier question.

## Missing primary counterpart

**#272:** Section 10 of its [manuscript](../problems/erdos-272/paper/proof.pdf) calls the full proof `Solution.lean` and the task-body version `submission/Main.lean`. Neither was included. The paper describes a 12,797-line standalone source; its reported checksum is copied into the [Lean record](../problems/erdos-272/lean/README.md) to help identify it.

## Materials needed to reproduce the Lean checks

The supplied sources are recorded as uploaded and not independently checked. None of the uploads includes a `lean-toolchain`, Lake project file, dependency manifest, `TaskSupport.lean`, or the earlier verification logs. The PDFs report versions and prior results; the per-problem Lean records preserve that provenance.

| Problem | Additional reproduction material described by the upload |
| :--- | :--- |
| [#14](../problems/erdos-14/lean/) | Separate task wrappers for the two bodies, imports, task support, and prior verification records. |
| [#96](../problems/erdos-96/lean/) | The original task wrapper or the 21-module project described in the PDF, its problem definitions, audit, manifest, and logs. |
| [#196](../problems/erdos-196/lean/) | Task wrapper and support; the standalone companion and index theorem described in the PDF are separate from the supplied body. |
| [#272](../problems/erdos-272/lean/) | The missing proof source plus its pinned task project and `verification.json`. |
| [#354](../problems/erdos-354/lean/) | Task project and support, `Audit.lean`, `verify.py`, and `verification.json`. |
| [#944](../problems/erdos-944/lean/) | Task project and support, `validation.json`, and the supplementary finite-check program described in the PDF. |

These support files are separate from the PDF/Lean pairing above. TeX, bibliography, and figure sources were not supplied for any manuscript. Submission and mathematical-review statuses remain recorded on each problem page.
