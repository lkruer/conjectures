# Conjectures

**Proof manuscripts and Lean formalizations for Erdős and Green problems.**

A home for manuscripts, formalizations, and review materials connected with [Erdős Problems](https://www.erdosproblems.com/) and [Ben Green’s *100 open problems*](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf). Each problem gets one page connecting its statement, proof PDF, Lean files, and submission history.

[Proof index](#proof-index) · [Add a proof](CONTRIBUTING.md) · [Erdős submission guide](docs/submission-guide.md)

## Proof index

**11 manuscripts · 11 Lean source files · 11 problem folders.** The [complete upload checklist](docs/upload-inventory.md#materials-still-to-upload) tracks all 12 entries on the author-provided list. One PDF and two Lean counterparts remain to be supplied.

The descriptions below reflect the uploaded materials. Manuscript-reported verification has not yet been independently reproduced in this repository.

| Problem | Result / title | Proof PDF | Lean | Submission |
| :--- | :--- | :--- | :--- | :--- |
| [Erdős #14](problems/erdos-14/) | Non-unique sums, parts I and II | [PDF](problems/erdos-14/paper/proof.pdf) | [2 files; not checked](problems/erdos-14/lean/) | Draft |
| [Erdős #96](problems/erdos-96/) | Unit distances in convex position | [PDF](problems/erdos-96/paper/proof.pdf) | [Source; not checked](problems/erdos-96/lean/) | Draft |
| [Erdős #108](problems/erdos-108/) | Counterexample via arc graphs | [PDF](problems/erdos-108/paper/proof.pdf) | [Source; not checked](problems/erdos-108/lean/) | Draft |
| [Erdős #196](problems/erdos-196/) | Permutations avoiding four-term progressions | [PDF](problems/erdos-196/paper/proof.pdf) | [Source; not checked](problems/erdos-196/lean/) | Draft |
| [Erdős #272](problems/erdos-272/) | Arithmetic-intersection families: linear error | [PDF](problems/erdos-272/paper/proof.pdf) | [Source; not checked](problems/erdos-272/lean/) | Draft |
| [Erdős #354](problems/erdos-354/) | Two floor-doubling sequences, part I | [PDF](problems/erdos-354/paper/proof.pdf) | [Source; not checked](problems/erdos-354/lean/) | Draft |
| [Erdős #944](problems/erdos-944/) | Critical graphs: existence for all k ≥ 4 | [PDF](problems/erdos-944/paper/proof.pdf) | [Source; not checked](problems/erdos-944/lean/) | Draft |
| [Green #15](problems/green-15/) | Lipschitz graph without three-term progressions | [PDF](problems/green-15/paper/proof.pdf) | [Source; not checked](problems/green-15/lean/) | Draft |
| [Green #40 (f(2))](problems/green-40/) | Binary linear covering codes of radius two | [PDF](problems/green-40/paper/proof.pdf) | **[Not uploaded](problems/green-40/lean/)** | Draft |
| [Green #47](problems/green-47/) | Exact quadratic-containment counterexample | [PDF](problems/green-47/paper/proof.pdf) | [Source; not checked](problems/green-47/lean/) | Draft |
| [Green #51 (1/2)](problems/green-51/) | Binary sumsets at density one half | [PDF](problems/green-51/paper/proof.pdf) | [Source; not checked](problems/green-51/lean/) | Draft |

## Inside each problem

Entries use `problems/erdos-<number>/` or `problems/green-<number>/`. The collection prefix keeps the two numbering systems distinct; parts and variants stay together inside their problem folder.

```text
problems/
└── <collection>-<number>/
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
| Listed on site | The relevant problem page references the result; the reference is recorded. |

Manuscript review and Lean verification are recorded separately on each problem page. A Lean upload starts as **not checked**; a passing build records the exact revision, theorem, and scope. See the [verification guide](docs/lean-verification.md).

## Adding or updating material

Use the [upload guide](CONTRIBUTING.md) for new manuscripts or revisions. The [upload checklist](docs/upload-inventory.md#materials-still-to-upload) identifies the remaining PDF and Lean counterparts. Original Lean project or task bundles can be added alongside the supplied sources to make their builds reproducible; the [inventory](docs/upload-inventory.md) records what is still needed.
