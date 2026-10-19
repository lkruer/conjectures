# Submission and source audit — 2026-10-18

[Proof index](../README.md#proof-index) · [Upload inventory](upload-inventory.md)

This record supplements the historical upload records at repository revision `e88dec4c88e42824b4acd3f9559febe67115471b`. It records public submission links, downloaded-source hashes, and correspondence checks made on 2026-10-18. It supersedes the older notes saying that no external submission had been recorded. It does not change the preserved manuscripts or claim a new local Lean build. Missing pinned projects and trusted wrappers remain listed in each problem's Lean record.

## JSP submissions located and reviewed

These are pull requests in [TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards). A linked PR is a submission record; its current review and merge status must be read on GitHub. The entries are not a claim that all submissions are merged or that every proof has been independently rebuilt.

| Problem | JSP entry | Pull request |
| :--- | :--- | :--- |
| Erdős #14 | JSP-000052 | [#4902](https://github.com/TheJustinSunPrize/awards/pull/4902) |
| Erdős #97 | JSP-000110 | [#289](https://github.com/TheJustinSunPrize/awards/pull/289) |
| Erdős #108 | JSP-000120 | [#4903](https://github.com/TheJustinSunPrize/awards/pull/4903) |
| Erdős #196 | JSP-000185 | [#4875](https://github.com/TheJustinSunPrize/awards/pull/4875) |
| Erdős #354 | JSP-000294 | [#5000](https://github.com/TheJustinSunPrize/awards/pull/5000) |
| Erdős #859 | JSP-000712 | [#4904](https://github.com/TheJustinSunPrize/awards/pull/4904) |
| Erdős #944 | JSP-000785 | [#5110, original-author submission](https://github.com/TheJustinSunPrize/awards/pull/5110); [#4668, related extension](https://github.com/TheJustinSunPrize/awards/pull/4668) |
| Erdős #1057 | JSP-000877 | [#4874](https://github.com/TheJustinSunPrize/awards/pull/4874) |
| Erdős #1062 | JSP-000882 | [#4905](https://github.com/TheJustinSunPrize/awards/pull/4905) |

The original-author #944 submission is [PR #5110, JSP-000785: original Kruer-Kohlmeyer solution and Lean proof](https://github.com/TheJustinSunPrize/awards/pull/5110), filed on 2026-10-18 from the author's [prepared materials](https://github.com/lkruer/conjectures/tree/codex/erdos944-prize-submission). Related extension PR #4668 is another contributor's submission using the credited original proof; it is a distinct filing. The JSP list and this repository's manuscript inventory are different sets: in particular, #97 is distinct from the #96 manuscript here.

## Accepted-source correspondence

The linked Conjectures.io records report external Lean verification and certification. Their downloadable accepted sources were fetched and compared with the repository files on the audit date. SHA-256 values below identify the **downloaded accepted bytes**, not a reconstructed project or, in rows with differences, the repository file. Repository-file hashes remain in each problem's `SHA256SUMS`.

| Entry / public certificate | Accepted-source SHA-256 | Relationship to repository source |
| :--- | :--- | :--- |
| [Erdős #14, part I](https://conjectures.io/results/dce3d778-6f52-4c27-8da0-c82d2f391b64) | `496840684dd5dc4f0747bf4732ee4fe246340353f8a11aae00bde325fa100ca5` | Byte-identical to [Erdos14_PartI.lean](../problems/erdos-14/lean/Erdos14_PartI.lean). |
| [Erdős #14, part II](https://conjectures.io/results/adb53fba-0b01-4398-abab-cb9b2176eebc) | `188ebf8bdf3a04694155ddf3e2d87c64f53d545781cfda7b63e21d6b1434cd74` | Byte-identical to [Erdos14_PartII_Counterexample.lean](../problems/erdos-14/lean/Erdos14_PartII_Counterexample.lean). |
| [Erdős #96](https://conjectures.io/results/7ffd1c09-2912-4c4c-a7ff-a4faa263f517) | `d445f7ec23d57a36ea4402c11eb8cc65fd6fd18ca1d6192e17f41cc359ea308c` | Byte-identical to [erdos96.lean](../problems/erdos-96/lean/erdos96.lean). |
| [Erdős #108](https://conjectures.io/results/8c083793-9c3c-4960-8a23-869e54fcb584) | `a0b65a62937486813884b5bbc9fb36a2bb6da42850a898126eddaecd5aaa0fa2` | Byte-identical to [Erdos108.lean](../problems/erdos-108/lean/Erdos108.lean). |
| [Erdős #196](https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73) | `e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826` | Byte-identical to [Erdos196.lean](../problems/erdos-196/lean/Erdos196.lean). |
| [Erdős #272](https://conjectures.io/results/c3277f4a-d573-42a9-bfca-e45fb2cb39ff) | `38201774f640e9c673b5e2a7821a1f031adf5bcf59ada9316fcde1f5455ba5bb` | Byte-identical to [Main.lean](../problems/erdos-272/lean/Main.lean). |
| [Erdős #354, part I](https://conjectures.io/results/815c1d5f-3afb-4430-8e2c-260d9038f5b0) | `7188a481c218751aa666a8577f0e6b1281462d4d3d97d548a565db99b44cc2ac` | [Erdos354.lean](../problems/erdos-354/lean/Erdos354.lean) adds only imports, an introductory comment, and the enclosing `Bounty` namespace. |
| [Green #15](https://conjectures.io/results/66df312f-30b4-4331-b1fa-04be52f7f8ca) | `d6f5d5e3a149ed8f3d65bf55084b94b00325a4d0ea0a94f1d3350dc155c754f8` | [Green15.lean](../problems/green-15/lean/Green15.lean) contains the accepted proof with additional attribution text and declarations listed below. |
| [Green #40, f(2)](https://conjectures.io/results/8186c13b-077f-45bb-8702-870f1dab27e3) | `3ce2c4e59100ad65a74ce35e457a1c0a8d8afe731b58e476c67ba609c7636be5` | Recovered byte-identically as [Main.lean](../problems/green-40/lean/Main.lean) in this update; see its [provenance record](../problems/green-40/lean/README.md). |
| [Green #47](https://conjectures.io/results/3f7ea330-0480-4e1a-b2fa-143440bf03b7) | `eddeff2c83de970aab5390fb0684a147712897ef4ed2e8b9cf755d4631152388` | Byte-identical to [Green47-COUNTEREXAMPLE-UPLOAD.lean](../problems/green-47/lean/Green47-COUNTEREXAMPLE-UPLOAD.lean). |
| [Green #51, one-half density](https://conjectures.io/results/217138ff-13fa-4110-9e7c-2e8533563988) | `95efbc149a5b09ff8f34a83fa673b5bd63b9591c071d9cf7a495182706ce5db3` | [green51onehalf.lean](../problems/green-51/lean/green51onehalf.lean) has the same proof text after accounting for added imports, the enclosing `Bounty` namespace, and line endings. |

The accepted-source endpoint for each record is its result URL followed by `/solution/download`. Exact byte equality was checked directly where stated; the other rows were compared as text to identify all additions. Green #15 adds `f_zero`, `incrementSet`, `finite_increment_mem`, `f_increment_mem`, `f_strictMono`, and `main_result`. The external certificate must not be extended to these added declarations without a repository replay.

The #108 PDF's `paper_main` and separate `arcGraph_triangle_free` declarations are absent from its accepted source, as already recorded in the [manuscript correspondence note](../problems/erdos-108/lean/README.md#manuscript-correspondence). The #196 standalone companion and Green #51 paper-theorem companions remain absent. Green #47's certificate addresses exact containment, not the version allowing finitely many exceptions. #354's certificate addresses part I with multiplier 2. These scope limits are unchanged.

## Repository checks and remaining work

All 23 entries in the problem checksum files match the stored PDF and Lean bytes after the Green #40 recovery. Existing manuscripts and existing Lean sources were not edited by this update. Source-identity checks and public certificate inspection are not fresh Lean compilation; local builds remain pending until the original pinned projects and trusted support files are supplied or separately reproduced and documented. A certificate of a historical target also does not establish compatibility with current upstream declarations.
