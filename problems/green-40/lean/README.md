# Lean formalization — Green #40

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md) · [Submission audit](../../../docs/submission-audit-2026-10-18.md)

**Status: Uploaded; not checked locally. External certification recorded below.**

## Recovered source and scope

[Main.lean](Main.lean) is the accepted Conjectures.io submission body, recovered on **2026-10-18** from the [public source download](https://conjectures.io/results/8186c13b-077f-45bb-8702-870f1dab27e3/solution/download). Its 39,122 bytes and 1,028 lines are preserved unchanged, including LF line endings and the final newline. The download's filename is `Main.lean`; Section 8 of the [manuscript](../paper/proof.pdf) calls its standalone companion `Green40.lean`.

SHA-256:

```text
3ce2c4e59100ad65a74ce35e457a1c0a8d8afe731b58e476c67ba609c7636be5
```

The final declaration, at lines 1025–1026, is `target : fcTypeOfName% "Green40.green_40.f_two_eq_one"`. The [public certificate](https://conjectures.io/results/8186c13b-077f-45bb-8702-870f1dab27e3) gives its target as `True ↔ Green40.f 2 = 1`.

The formal target concerns covering radius at most two. The paper’s additional observation about exact radius two is described separately in the proof of Theorem 1.1.

The file's header says the trusted task supplies `FormalConjectures.GreensOpenProblems.«40»`, `TaskSupport`, and the surrounding `Bounty` namespace. It is a submission body, not a standalone project. The contributed sphere-covering lower bound `Contribution.Green40FTwoEqOne.one_le_f` is included within the file.

## External certificate and reported environment

Conjectures.io credits **JenW1N**, records verification on **2026-09-15**, review approval on **2026-09-16**, and certification on **2026-09-17**. It reports passing production Lean verification and permitted-axiom checks. Nanoda was not run. These are the platform's results for the accepted bytes, not a new repository build or certification of the manuscript's prose.

The source and manuscript identify Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

| Public record field | Value |
| :--- | :--- |
| Task | `fc-8432eac9-green-40-f-two-eq-one-ce69be0661-formalized-v1` |
| Task bundle SHA-256 | `979abda716baba300e7d3d09476ff301401d93abb906d64be384c33765fe94ca` |
| Verifier | `validator-e6c06c0a725003f5e5cedf792d49935a3cac8146` |
| Report SHA-256 | `bc4bca7841e1b8f153c6bfaaca855bd2693c6f4d7bbbd91a3c5c86af8b8a3393` |
| Permitted axioms | `propext`, `Quot.sound`, `Classical.choice` |

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | No local build |
| Build commands executed | None |
| Build result / kernel audit | Not run locally |
| Target inspection | Final target and public certificate compared; no local elaboration |
| File integrity | Download SHA-256 matches the stored file and [SHA256SUMS](../SHA256SUMS) |

## Materials still needed

The original pinned project with `lean-toolchain`, Lake configuration and dependency manifest, trusted wrapper, `TaskSupport`, and the local verification record and reproduction instructions described in manuscript Section 8 have not been added. The downloaded source does not replace those materials. Keep local verification pending until an actual build and axiom audit are recorded.
