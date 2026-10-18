# Reproducible Erdős 944 proof

Authors of the original proof and accompanying manuscript: **Liam Kruer (`lkruer`) and Jensen Kohlmeyer (`JENW1N`)**. OpenAI Codex assisted with proof development, Lean formalization, and preparation of this verification package.

`Solutions/Erdos944.lean` is copied unchanged from `JENW1N/complete-math-solutions` commit `caa0b07847cc94a071215de82036be4b5805ee0c`. Its proof body is the accepted source at `accepted/erdos944.lean` in that commit, retained here as `accepted-proof-body.lean.txt`. This source differs from the older historical `../erdos944.lean`; the older file is preserved separately and is not represented as byte-identical.

The 191 local import files needed by that solution are vendored, including the Formal Conjectures definitions and helper modules. The exact list is in `local-import-closure.json`. No other Erdős problem solution is required.

## Verify

Install [elan](https://github.com/leanprover/elan), make `lean` and `lake` available in `PATH`, then run:

```sh
./verify.sh
```

`lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins mathlib to `0df444a360eaa60ab8c11dca51a86af692955474` and fixes every package revision. The cache step downloads compiled dependencies; the local proof and wrapper are checked by Lean. The script writes the tool versions, build log, and axiom audit to `verification/`.

`Erdos944Prize.target` states the mathematical assertion directly, without `answer` syntax: for all `k ≥ 4` and `r ≥ 1`, a finite vertex-critical graph of chromatic number `k` exists for which every chromatic-number-reducing edge set has more than `r` elements. `Erdos944Prize.finite_all` also covers `r = 0`. The finite wrapper follows the witnesses already constructed in the original proof and retains their finiteness.

`Erdos944Prize.benchmark_type_check` checks that the positive answer also has exactly the original benchmark's elaborated type. The imported Formal Conjectures file contains the usual unsolved theorem placeholders, but the axiom audit checks that the solution does not depend on them. `AxiomAudit.lean` checks every proof declaration's transitive axioms and fails if any axiom outside `propext`, `Classical.choice`, or `Quot.sound` is found.

See `THIRD-PARTY-NOTICES.md` for the scope of the copied Apache license notices. Successful local verification establishes the recorded Lean result; prize eligibility, attribution, and any award remain decisions of the prize organizers.
