# Upload inventory

[Back to the proof index](../README.md#proof-index)

The repository contains **eleven PDFs and eleven originally supplied Lean source files across eleven problem folders**, plus the Erdős 196 reproduction package. The author’s current list contains **12 entries: eight Erdős problems and four Green problems**. This inventory records file availability and the supplied scope labels; proof verification is tracked separately.

## Materials still to upload

**One PDF and two Lean counterparts remain.**

| Problem | Still needed |
| :--- | :--- |
| Erdős #18 | PDF and Lean |
| [Green #40 (f(2))](../problems/green-40/) | Lean only (`Green40.lean`, as named in the PDF) |

These totals count missing PDF/Lean counterparts. Erdős 108 has both, but its PDF references `paper_main` and `arcGraph_triangle_free`, which are absent from the previously uploaded Lean file. A matching source revision or clarification is still needed; see the [source correspondence record](../problems/erdos-108/lean/README.md#manuscript-correspondence). Additional project and verification materials are tracked separately below.

## Complete list supplied by the author

| Problem | Scope / variant | PDF | Lean |
| :--- | :--- | :--- | :--- |
| [Erdős #14](../problems/erdos-14/) | Parts I and II | [Present](../problems/erdos-14/paper/proof.pdf) | [2 files](../problems/erdos-14/lean/) |
| Erdős #18 | As listed by the author | **Not supplied** | **Not supplied** |
| [Erdős #96](../problems/erdos-96/) | Convex unit distances | [Present](../problems/erdos-96/paper/proof.pdf) | [1 file](../problems/erdos-96/lean/) |
| [Erdős #108](../problems/erdos-108/) | Counterexample via arc graphs | [Present](../problems/erdos-108/paper/proof.pdf) | [1 file; correspondence note](../problems/erdos-108/lean/) |
| [Erdős #196](../problems/erdos-196/) | Four-term progression counterexample | [Present](../problems/erdos-196/paper/proof.pdf) | [Original source and reproduction package](../problems/erdos-196/lean/) |
| [Erdős #272](../problems/erdos-272/) | Szabó strong variant | [Present](../problems/erdos-272/paper/proof.pdf) | [1 file](../problems/erdos-272/lean/) |
| [Erdős #354](../problems/erdos-354/) | Part (i), multiplier 2 | [Present](../problems/erdos-354/paper/proof.pdf) | [1 file](../problems/erdos-354/lean/) |
| [Erdős #944](../problems/erdos-944/) | Existence statement | [Present](../problems/erdos-944/paper/proof.pdf) | [1 file](../problems/erdos-944/lean/) |
| [Green #15](../problems/green-15/) | Lipschitz graph | [Present](../problems/green-15/paper/proof.pdf) | [1 file](../problems/green-15/lean/) |
| [Green #40](../problems/green-40/) | f(2) = 1 | [Present](../problems/green-40/paper/proof.pdf) | **Not supplied** |
| [Green #47](../problems/green-47/) | Exact-containment formulation | [Present](../problems/green-47/paper/proof.pdf) | [1 file](../problems/green-47/lean/) |
| [Green #51](../problems/green-51/) | One-half density (1/2) | [Present](../problems/green-51/paper/proof.pdf) | [1 file](../problems/green-51/lean/) |

## Original filenames received

| Problem | Original PDF filename | Pages | Original Lean filename(s) |
| :--- | :--- | ---: | :--- |
| [Erdős #14](../problems/erdos-14/) | `Erdos14_Unified_Paper.pdf` | 8 | `Erdos14_PartI.lean`, `Erdos14_PartII_Counterexample.lean` |
| [Erdős #96](../problems/erdos-96/) | `erdos96-convex-unit-distances.pdf` | 8 | `erdos96.lean` |
| [Erdős #108](../problems/erdos-108/) | `erdos108-arc-graphs.pdf` | 8 | `Erdos108.lean` |
| [Erdős #196](../problems/erdos-196/) | `Erdos196-Kohlmeyer-Kruer (1).pdf` | 7 | `Erdos196.lean` |
| [Erdős #272](../problems/erdos-272/) | `erdos272-linear-error (1).pdf` | 15 | `Main.lean` |
| [Erdős #354](../problems/erdos-354/) | `erdos354-Kohlmeyer-Kruer.pdf` | 13 | `lean354` |
| [Erdős #944](../problems/erdos-944/) | `erdos944-kruer-kohlmeyer (2).pdf` | 13 | `erdos944.lean` |
| [Green #15](../problems/green-15/) | `Green15-Kohlmeyer-Kruer.pdf` | 8 | `Green15.lean` |
| [Green #40](../problems/green-40/) | `green40-covering-codes.pdf` | 8 | **Not supplied** |
| [Green #47](../problems/green-47/) | `Green47-Kohlmeyer-Kruer (2).pdf` | 7 | `Green47-COUNTEREXAMPLE-UPLOAD.lean` |
| [Green #51](../problems/green-51/) | `green51-one-half (1).pdf` | 7 | `green51onehalf.lean` |

## File handling and scope

- PDFs are stored as `paper/proof.pdf` in each problem folder. Uploaded PDF and Lean contents are preserved byte for byte; each folder includes `SHA256SUMS`.
- The extensionless `lean354` is stored as `Erdos354.lean`. All other uploaded Lean filenames are retained.
- Erdős 14 has one unified PDF and two Lean files together in `erdos-14/`.
- Erdős 354 covers part (i), multiplier 2. Green 40 is listed specifically for f(2), and Green 51 for the one-half-density question.
- Green 47’s PDF and source address exact containment. They explicitly exclude the version allowing finitely many exceptional elements.
- Erdős 272’s `Main.lean` is the supplied submission body; its original wrapper is still needed for reproduction.
- Green 15’s `Green15.lean` is a submission body whose validator supplies imports and the enclosing namespace. Green 51’s `green51onehalf.lean` includes its imports and `Bounty` namespace; its filename is preserved even though the manuscript calls the main proof `Solution.lean`.

## Materials needed to reproduce the Lean checks

Erdős 196 has a fresh local compilation and axiom-audit record with recovered task support and pinned dependencies. The other uploaded Lean sources have not been independently compiled here. Original toolchain/project files, task support, and the verification records described by those manuscripts were not included. The following support files are separate from the PDF/Lean counterpart checklist above.

| Problem | Additional reproduction material described by the upload |
| :--- | :--- |
| [Erdős #14](../problems/erdos-14/lean/) | Separate task wrappers for the two bodies, imports, task support, and prior verification records. |
| [Erdős #96](../problems/erdos-96/lean/) | The original task wrapper or the 21-module project described in the PDF, its problem definitions, audit, manifest, and logs. |
| [Erdős #108](../problems/erdos-108/lean/) | Source revision or clarification for the PDF’s `paper_main` and `arcGraph_triangle_free`; original task wrapper and support, pinned Lean project, and verification record containing full dependency revisions and the checked artifact digest. |
| [Erdős #196](../problems/erdos-196/lean/) | Recovered wrapper, exact pinned dependency reconstruction, and fresh audit are now provided. See the reproduction package for the separate October 8 index corollary and the limits of historical verification claims. |
| [Erdős #272](../problems/erdos-272/lean/) | The task wrapper, pinned project, `TaskSupport`, and `verification.json` for the supplied submission body. |
| [Erdős #354](../problems/erdos-354/lean/) | Task project and support, `Audit.lean`, `verify.py`, and `verification.json`. |
| [Erdős #944](../problems/erdos-944/lean/) | Task project and support, `validation.json`, and the supplementary finite-check program described in the PDF. |
| [Green #15](../problems/green-15/lean/) | Main source present. The trusted `SolutionHeader.lean.txt` and `SolutionFooter.lean.txt`, original task/project configuration, and validation record remain to be supplied. |
| [Green #40](../problems/green-40/lean/) | The PDF names `Green40.lean` as the main proof. Also supply the original pinned project, `TaskSupport`, and the verification record and reproduction instructions described in Section 8. |
| [Green #47](../problems/green-47/lean/) | The main submission body is present. The original task wrapper, problem definitions, `TaskSupport`, pinned project, standalone companion, and verification reports were not included. |
| [Green #51](../problems/green-51/lean/) | Main source present as `green51onehalf.lean` (1,925 lines). The manuscript’s `PaperTheorem.lean`, `CheckGreen51.lean`, pinned task project with `TaskSupport`, and companion verification report remain to be supplied. |

TeX, bibliography, and figure sources were not supplied as separate files. Submission and review statuses remain recorded on each problem page.
