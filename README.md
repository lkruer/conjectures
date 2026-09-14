# Conjectures

**Proof manuscripts and Lean formalizations for Erdős Problems.**

A home for work in progress, completed manuscripts, and the materials shared for review on [Erdős Problems](https://www.erdosproblems.com/). Each problem gets one page connecting its statement, proof PDF, Lean files, and submission history.

[Proof index](#proof-index) · [Add a proof](CONTRIBUTING.md) · [Submission guide](docs/submission-guide.md)

## Proof index

**6 manuscripts · 6 Lean source files across 5 problems.** The Lean counterpart for **#272** is still missing. See the [upload inventory](docs/upload-inventory.md) for original filenames and reproduction materials still needed.

The descriptions below reflect manuscript claims. The manuscripts report prior formal verification; those checks have not yet been independently reproduced in this repository.

| Problem | Result / title | Proof PDF | Lean | Submission |
| :--- | :--- | :--- | :--- | :--- |
| [#14](problems/erdos-14/) | Non-unique sums, parts I and II | [PDF](problems/erdos-14/paper/proof.pdf) | [2 files; not checked](problems/erdos-14/lean/) | Draft |
| [#96](problems/erdos-96/) | Unit distances in convex position | [PDF](problems/erdos-96/paper/proof.pdf) | [Source; not checked](problems/erdos-96/lean/) | Draft |
| [#196](problems/erdos-196/) | Permutations avoiding four-term progressions | [PDF](problems/erdos-196/paper/proof.pdf) | [Source; not checked](problems/erdos-196/lean/) | Draft |
| [#272](problems/erdos-272/) | Arithmetic-intersection families: linear error | [PDF](problems/erdos-272/paper/proof.pdf) | **[Missing](problems/erdos-272/lean/)** | Draft |
| [#354](problems/erdos-354/) | Two floor-doubling sequences, part I | [PDF](problems/erdos-354/paper/proof.pdf) | [Source; not checked](problems/erdos-354/lean/) | Draft |
| [#944](problems/erdos-944/) | Critical graphs: existence for all k ≥ 4 | [PDF](problems/erdos-944/paper/proof.pdf) | [Source; not checked](problems/erdos-944/lean/) | Draft |

## Inside each problem

Every entry lives in `problems/erdos-<number>/`, using the number from the Erdős Problems website.

```text
problems/
└── erdos-<number>/
    ├── README.md          # Statement, result, authors, and review status
    ├── paper/
    │   ├── proof.pdf      # Current manuscript, added when supplied
    │   └── ...            # Optional TeX, bibliography, and figures
    ├── lean/
    │   └── ...            # Lean sources, pinned environment, and build notes
    └── submission.md      # Prepared announcement and submission history
```

The reusable starting point is in [templates/problem](templates/problem/). The [upload guide](CONTRIBUTING.md) explains naming and updates.

## Progress at a glance

| Submission status | Meaning |
| :--- | :--- |
| Draft | The manuscript or review is still in progress. |
| Ready to submit | The author has completed the submission checklist and prepared the links. |
| Submitted | A link has been posted or sent; the date and destination are recorded. |
| Listed on site | The Erdős Problems page references the result; the reference is recorded. |

Manuscript review and Lean verification are recorded separately on each problem page. A Lean upload starts as **not checked**; a passing build records the exact revision, theorem, and scope. See the [verification guide](docs/lean-verification.md).

## Adding or updating material

Use the [upload guide](CONTRIBUTING.md) for new manuscripts or revisions. The next missing proof counterpart is **Lean for #272**. Original Lean project or task bundles can be added alongside the supplied sources to make their builds reproducible; the [inventory](docs/upload-inventory.md) records what is still needed.
