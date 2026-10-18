# Lean formalization — Erdős #944

[Back to the problem](../README.md) · [Source history](../SOURCE_HISTORY.md) · [Reproduction package](reproducible/)

The original authors are **Liam Kruer (`lkruer`) and Jensen Kohlmeyer (`JENW1N`)**. OpenAI Codex assisted with proof development and formalization. The higher-color mathematics of Skottová and Steiner retains its attribution.

## Sources

| Source | Role |
| --- | --- |
| [erdos944.lean](erdos944.lean) | Historical September standalone source, preserved unchanged. Its original upload lacked the full task environment. |
| [reproducible/](reproducible/) | Exact accepted proof body, standalone wrapper, explicit finite-existence statement check, frozen local reference sources, and pinned Lean/Mathlib dependencies. |

These sources are different versions. The historical file’s SHA-256 is `b89b43ce3470e9a3c51164f58f401a038260b0493e167fb6d8a5cf608bffd630`; the accepted proof body’s SHA-256 is `8bf7cd0e83463e5f304ad848921c5078d57e8f3411050e705c69a69822abecd5`. The difference includes proof details, not just imports. Do not transfer a verification claim between versions without checking the selected version.

## Statement

The original target is `Bounty.target`, matching the frozen Formal Conjectures statement for Erdős 944. The package also checks a literal statement of finite graph existence for every `k ≥ 4` and `r ≥ 1`. The underlying predicate requires vertex criticality and that every edge set whose deletion lowers the chromatic number has cardinality greater than `r`.

The statement is existence of a graph for each pair of parameters. It does not assert existence at every sufficiently large order; peilinliu66-dev’s later prescribed-order extension remains separately credited.

## Reproduction and verification

Use the [package README](reproducible/README.md) for exact commands, source integrity checks, and actual recorded results. The package pins Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and includes the required frozen task/reference sources with their notices.

Reference conjecture files retain their original admitted statements. They are reference material, not accepted proof dependencies: every submitted final theorem must have a transitive axiom report containing only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or added assumptions. The explicit statement check makes the submitted conclusion inspectable independently of the reference file’s answer notation.

Local compiler and axiom checks are evidence for review. They do not constitute an independent human proof review, a Justin Sun Prize verification, or an award decision.
