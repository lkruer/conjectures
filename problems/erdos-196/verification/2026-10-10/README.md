# October 10 verification evidence

[Full report](report.md) · [Completion and priority statement](../../PRIORITY.md) · [Source-identity check](source-identity-result.json)

This directory preserves the completed check of proof commit `bf058b903350eb8f873a22ab4a54b2e0faa9727d`. The source-build and audit drivers, raw logs, standard-axiom verdicts, independent checker configuration and source-built checker provenance are included. The later publication adds evidence and documentation; it does not revise the proof. The recorded paths identify the actual local run and can be adapted to another checkout. The project's portable reproduction instructions remain in `../../lean/reproduction/REPRODUCING.md`.

`service-download.lean` preserves the accepted-source bytes retrieved during the review. `verify_source_identity.py` compares those bytes with the original Git object, selected payload and checked wrapper. It authenticates byte identity, not the service's historical date.

The large proof export is identified by SHA-256 and an exact regeneration command in `result.json`; it remains in the local audit archive and is not duplicated here. Compiler output is preserved verbatim, including its diagnostic whitespace and the recorded initial failed invocation. `SHA256SUMS` covers this directory. These records do not constitute Prize acceptance or independent human peer review.
