# Erdős 944: source history and attribution

This record distinguishes the original mathematical contribution, the public proof versions, and the later work needed to reproduce them. A new packaging commit does not replace the earlier public history or establish a new discovery date.

## Authors and scope

**Liam Kruer (`lkruer`) and Jensen Kohlmeyer (`JENW1N`)** are the authors of the accompanying mathematical manuscript and the original Lean proof. The manuscript acknowledges OpenAI Codex assistance with mathematical development, formalization, and preparation.

The result is existence, for every integer `k ≥ 4` and `r ≥ 1`, of a finite `k`-vertex-critical graph whose chromatic number is not reduced by deleting at most `r` edges. Theorem 1.1 of the manuscript proves the four-color construction; Corollary 1.2 combines it with the earlier higher-color result of **Ema Skottová and Raphael Steiner**. The Lean development supplies the all-color existence proof.

The original existence result does not claim that every sufficiently large graph order is attainable. **peilinliu66-dev's later prescribed-order extension and its integration retain their separate credit.** Earlier `k=4, r=1` work by Alex Chan and Kenta Kitamura also retains its credit; neither that special case nor prior higher-color work is claimed here as a new discovery by Kruer and Kohlmeyer.

## Public records

| Record | Date and meaning | Reference |
| --- | --- | --- |
| Original manuscript | Printed date: 10 September 2026. A manuscript date alone is not proof of public disclosure. | [Preserved PDF](paper/proof.pdf), Theorem 1.1, Corollary 1.2, and Section 8 |
| Conjectures.io acceptance | The service records 11 September 2026, 21:06:04 UTC as acceptance of the full result. This is a service verification date, not a Justin Sun Prize decision. | [Result and review](https://conjectures.io/results/e7afff2c-bb07-4fa8-92b6-67a530aaad70) |
| Original author repository | The commit introducing the original standalone proof is dated 14 September 2026, 03:39:34 UTC. This differs from the date-only upload note previously written in the README. | [Commit 8ede860e8fc90a300207a2c17e8aefe6167b3086](https://github.com/lkruer/conjectures/commit/8ede860e8fc90a300207a2c17e8aefe6167b3086) |
| Conjectures.io certification | The service records public certification on 16 September 2026. Its reward is separate from the Justin Sun Prize. | [Certified result](https://conjectures.io/results/e7afff2c-bb07-4fa8-92b6-67a530aaad70) |
| Coauthor's reproducible edition | The 10 October edition preserves the accepted proof body, supplies its task environment, and records a local compilation and target-axiom inspection. | [Pinned coauthor source edition](https://github.com/JENW1N/complete-math-solutions/tree/a624e9de77e0bd8868e7103f8b379f9dbd86b607) |
| Current author-controlled package | Reproduction in this repository adds a complete pinned environment and explicit statement checks. Its new commit date is not an original proof-completion date. | [Reproduction package](lean/reproducible/) |

## File identities

| Artifact | SHA-256 |
| --- | --- |
| Preserved original PDF, also served by `https://jenwin.io/papers/erdos-944.pdf` | `77e311d97357f98fc33db89ddd63ca6fc3fc5c610bf90075cd9dc1077922ecb8` |
| Original September standalone Lean file, retained at `lean/erdos944.lean` | `b89b43ce3470e9a3c51164f58f401a038260b0493e167fb6d8a5cf608bffd630` |
| Exact accepted Conjectures.io proof body, retained in the reproduction package | `8bf7cd0e83463e5f304ad848921c5078d57e8f3411050e705c69a69822abecd5` |

The original standalone file and the accepted proof body are **different versions**. They differ in comments, wrapper material, and proof details. They must not be described as byte-identical. The manuscript's Section 8 describes 570 theorems in the historical 9,548-line standalone file. The accepted body instead contains 572 theorem declarations in 9,535 lines. The new package preserves that accepted body without mathematical edits and identifies the added imports, namespace, and statement-audit wrapper separately. See its integrity manifest and reproduction report for the exact tested files. The manuscript's historical verification claims are not transferred to the changed source by assertion.

## Justin Sun Prize review

The correct catalog identifier is **JSP-000785**, not JSP-000944. The original-author submission requests review of both mathematical and formalization contributions, with both authors credited. [PR #4668](https://github.com/TheJustinSunPrize/awards/pull/4668) separately submits peilinliu66-dev's prescribed-order extension and integration; [Jensen's source-registration comment](https://github.com/TheJustinSunPrize/awards/pull/4668#issuecomment-6094312797) already identifies the original proof.

The organizers must independently determine correctness, scope, authorship, priority, eligibility, and any award. A successful local compilation does not settle those questions. No author identity checks, recipient confirmations, prize allocation, or payment are represented as complete by this record.
