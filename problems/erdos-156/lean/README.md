# Erdős 156: reproducible Lean project

This project proves the affirmative answer to Erdős problem 156: for every sufficiently large N, there is an inclusion-maximal Sidon subset of {1,...,N} with cardinality O(N^(1/3)). Diagonal pair sums are included in the Sidon convention.

## Authors

Will Howe (@h0w4rd), Grant Huffman (@ghuffy), Jensen Kohlmeyer (@jenw1n), and Liam Kruer (@lkruer). The submitting author reports that all four contributed to both the mathematical solution and the Lean formalization. OpenAI Codex assisted with mathematics, formalization, exposition, and this verification/package preparation.

## Reproduce

Install the official Lean toolchain specified by `lean-toolchain`, then run from this directory:

```sh
lake exe cache get
lake build +Main
lake env lean Erdos156.lean
lake env lean Audit.lean
lake env lean AuditAll.lean
```

Retain `lake-manifest.json`; it pins mathlib and every transitive package. Mathlib is fixed at `065356127b1dc0016f66b7283ce0ce2c4055aa55`, with Lean `4.35.0-rc2`.

The theorem answering the original question is `Erdos156.solved` in `Main.lean`. `Bounty.target` retains the challenge's equivalent `True ↔ ...` formulation. `IndependentAudit.original_question` expands interval containment, the full Sidon condition, inclusion maximality, and the uniform asymptotic bound.

## Relationship to the supplied files

`originals/Erdos156Submission.lean` is the supplied upload payload, preserved byte for byte. To make it independently buildable, `Erdos156.lean` adds the enclosing `Bounty` namespace and imports `Statement.lean`. It restores the companion file's exponentiation threshold (1024) as a wrapper option. The only changes inside the payload are two replacements of the website-specific `fcTypeOfName% "Erdos156.erdos_156"` expression by its explicit `True ↔` asymptotic proposition (also recorded as `Erdos156.Target` in `Statement.lean`). No mathematical proof steps have been changed.

`originals/Erdos156.lean` is the complete companion file whose SHA-256 appears in the manuscript. It is also preserved byte for byte. It differs from the supplied upload payload in namespace wrappers, simplifier attributes, and explicit elaboration steps. The new verification concerns the portable project, not a claimed reproduction of the unavailable original challenge bundle.

The definitions of `IsSidon`, `Set.IsMaximalSidonSetIn`, and `Erdos156.minMaximalSidonSet` agree with the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/156.lean) and its [supporting definitions](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjecturesForMathlib/Combinatorics/Basic.lean). They are included locally without importing any unproved conjecture.

See `verification/report.md` for the actual checks, limitations, and axiom audit. The original files' hashes are in `originals/SHA256.json`. Verification and submission for review do not constitute acceptance or an award.
