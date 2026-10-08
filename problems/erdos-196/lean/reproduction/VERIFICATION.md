# Verification record — October 8, 2026

**Passed.** The unchanged clean payload, the required wrapper, and the new direct-statement corollary compile with Lean 4.33.1. The complete scripted run ended with `Build and axiom audit passed.`

Test command from this directory: `python3 scripts/reproduce.py --skip-cache`. Existing dependency artifacts were reused. The script freshly compiled the pinned problem declaration in `google.answer=always_true` mode, `Erdos196.lean`, and `PaperMain.lean`, then ran `lake env lean --trust=0 Audit.lean`. The bootstrap had separately reconstructed the exact pinned commit from the public official base and the supplied patch. A fresh download of all dependency caches was not repeated.

The [recorded command results](verification/results.json) contain exit code 0 for every step. The [audit output](verification/audit.log) and [machine-readable result](verification/audit-result.json) show exactly `propext`, `Classical.choice`, and `Quot.sound` for each of:

- `Bounty.target`
- `Bounty.paper_main`
- `Bounty.Construction196.counterexample`
- `Bounty.Construction196.finite_extension`
- `Bounty.Construction196.permFun_injective`
- `Bounty.Construction196.permFun_surjective`
- `Bounty.Construction196.permFun_no_four`

The proof and corollary compilation logs are empty, indicating no warnings or errors. Compiling the original problem statement reports its expected admitted-theorem warning. The axiom audit confirms that this admitted theorem body is not a dependency of any audited result.

The payload's SHA-256 is `e65c98a926ce4eca5df30277790c8b3dbcc630074ceaa24a551464951b3d2826`. It is byte-identical to the user-supplied `Main (2).lean`, the pre-existing portfolio copy, and `originals/Erdos196-submission.lean`. The wrapper adds imports and an outer namespace and relocates the unchanged header comment. No mathematical proof step was modified.

This is a reproducible Lean compilation and axiom audit, not an independent mathematical review, a JSP acceptance decision, or a claim that the complete historical service validator was rerun.
