# Erdős 944 Lean verification

Result: **verified** at 2026-10-18T19:57:21.116912+00:00.

- Repository commit: `d42416ace335b42e05c6f46d250c869bce4b5239`.
- Source manifest SHA-256: `c5e22b947f29031855ad19a00224d2fe19f9b33f058ea3eb26c6cbea0cc1d929` (`SOURCE_SHA256SUMS`).
- Lean: `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`.
- Pinned mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Targeted build: `lake build PrizeSubmission AxiomAudit` succeeded.
- Transitive axiom audit: **2339 declarations passed**; no `sorryAx` or additional axioms. The permitted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`Erdos944Prize.target` explicitly proves the requested finite graph exists for every `k ≥ 4` and `r ≥ 1`; `finite_all` also covers `r = 0`. `benchmark_type_check` has exactly the elaborated original Formal Conjectures type. The imported problem stub contains placeholders, but the successful audit establishes that the proof does not depend on them.

The original accepted proof body and its `Solutions/Erdos944.lean` wrapper matched their recorded source hashes. This is a successful Lean build and dependency audit, not a prize-award or priority decision. Full command output and all dependency revisions are retained beside this report.
