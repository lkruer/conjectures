# Reproduce the Erdős 196 counterexample

Authors of the submitted mathematics and Lean proof: Jensen Kohlmeyer (`jenw1n`) and Liam Kruer (`lkruer`).

## Run

Install Git, Python 3, and Elan, with `lake` on PATH. Run from this directory:

```sh
python3 scripts/reproduce.py
```

The script reconstructs the exact original Formal Conjectures commit, obtains the pinned Mathlib cache, compiles the supplied proof, and runs the axiom audit with Lean `--trust=0`. Results go to `reproduction-logs/`. If all dependency artifacts are already present, `python3 scripts/reproduce.py --skip-cache` performs the same compilation and audit without downloading the cache.

Use this script rather than plain `lake build`: the pinned Formal Conjectures project also defines an `AnswerPostpone` library for the same problem modules. The script explicitly compiles problem 196 with `-Dgoogle.answer=always_true`, matching the original validator's affirmative-statement target. It does not modify the problem declaration or any proof step.

## Inputs and packaging

- `originals/Erdos196-submission.lean` is the unchanged clean submission body, also supplied by the user as `Main (2).lean` on October 8, 2026.
- `originals/pasted-2026-10-08.txt` preserves the encoding-damaged paste. `provenance/encoding-repair.json` records an exact byte-level correspondence with the clean body.
- `Erdos196.lean` adds only the imports and outer `Bounty` namespace described in the original header; the original header is placed after the imports as the module docstring.
- `PaperMain.lean` is a new short corollary restating the manuscript's Theorem 1.1 directly in terms of four increasing indices. It invokes the supplied bijectivity and `permFun_no_four` lemmas. It is not a recovered copy of the historical standalone companion mentioned in the manuscript.
- `Audit.lean` prints the target, the direct statement, and the transitive axiom sets of seven declarations.
- `TaskSupport.lean` is unchanged support code from `conjectures-io/conjectures-validator` commit `c36660f7ddd212eb5d253853adb92b928dcb0581`, file `lean/TaskSupport.lean` (SHA-256 `58a80a223dbd7383d92eb2a57b1ec207c0991131a1a1bf24585a4452777c257e`). It provides the syntax that retrieves the type of the named problem declaration.

## Pinned environment

Lean `4.33.1`, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. `lake-manifest.json` locks the full dependency graph.

Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142` is a validator-generated commit, not an object served by the official repository. `scripts/bootstrap.py` fetches official base `7d1a8c9912747679d0093f6d1216420c33ee5ffa`, applies `provenance/formal-conjectures.patch`, verifies tree `88827a7ca9495954133c8549ea5e9d86acc7325a`, and reconstructs and verifies the original commit object. The patch touches eight other problem files; problem 196 is unchanged. `validator-pins.lock.json` preserves the historical pin record. The newly exported patch has its own SHA-256; it need not match the historical patch file's byte representation to reconstruct the identical tree and commit.

## Interpreting the audit

The exact target is `¬ (True ↔ ∀ f : ℕ ≃ ℕ, HasMonotoneAP f 4)`. This refutes the affirmative answer. `Construction196.counterexample` directly supplies a permutation with no monotone four-term arithmetic progression, and `Bounty.paper_main` spells out the two prohibited arithmetic equalities.

The expected transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The audit rejects any other axiom. In particular, the admitted theorem body in the source statement repository is not a proof dependency: the submission uses its type only. The run is a Lean compilation and trust-level-zero axiom audit; it is not a claimed independent JSP review or a replay of the entire historical service validator.
