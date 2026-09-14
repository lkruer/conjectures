# Conjectures

**Proof manuscripts and Lean formalizations for Erdős Problems.**

A home for work in progress, completed manuscripts, and the materials shared for review on [Erdős Problems](https://www.erdosproblems.com/). Each problem gets one page connecting its statement, proof PDF, Lean files, and submission history.

[Proof index](#proof-index) · [Add a proof](CONTRIBUTING.md) · [Submission guide](docs/submission-guide.md)

## Proof index

No proofs have been uploaded yet. Manuscripts can be added first; Lean formalizations can follow when available.

| Problem | Result / title | Proof PDF | Lean | Submission |
| :--- | :--- | :--- | :--- | :--- |
| — | Awaiting the first manuscript | — | — | — |

<!-- Replace the empty-state row when the first proof is added. Sort by numeric problem ID. Link each problem to its folder and each PDF directly to the file. -->

## Inside each problem

Every entry will live in `problems/erdos-<number>/`, using the number from the Erdős Problems website.

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

## Sending the next proof

Start with the **PDF and Erdős problem number**. Include the preferred title, author names, and whether the result is a full solution, a partial result, or another kind of contribution. The Lean files and their original project configuration can be added afterward.
