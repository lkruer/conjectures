# Submission notes — Green #40, f(2)

[Back to the problem](README.md)

**Status: External certificate recorded.** [Current record](https://conjectures.io/results/8186c13b-077f-45bb-8702-870f1dab27e3) · [Dated audit](../../docs/submission-audit-2026-10-18.md)

| Item | Record |
| :--- | :--- |
| Problem source | [Ben Green, *100 open problems*](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), Problem 40 |
| Manuscript | [PDF](paper/proof.pdf), September 15, 2026 |
| Authors | Jensen Kohlmeyer and Liam Kruer |
| Lean | [Accepted submission body](lean/Main.lean), recovered unchanged on 2026-10-18; see the [Lean record](lean/README.md). |
| Submission destination | [Conjectures.io result](https://conjectures.io/results/8186c13b-077f-45bb-8702-870f1dab27e3) |
| Proof snapshot | Public accepted-source download and SHA-256 recorded in the Lean record; manuscript announcement links are not frozen. |

## Summary for author review

**Result:** The manuscript claims f(2) = 1 through a sequence of binary linear codes of covering radius at most two and density tending to one. The scope is the radius-two question.

**Proof idea:** Iterated quadratic maps and a repair of their graphs provide additive sum bases; parity-check columns turn these into covering codes with the required density limit.

**Verification:** Local checks are reported in Section 8. The public Conjectures.io certificate records passing verification for its accepted submission body. Repository reproduction has not been performed.

## Before sharing

- [x] Recover and checksum the accepted Lean submission body.
- [ ] Supply the supporting project files and trusted wrapper for local reproduction.
- [ ] Complete author review of the argument and exact problem formulation.
- [ ] Confirm the evidence and scope behind formal-verification claims.
- [ ] Record the intended destination and prepare the announcement, acknowledgments, and commit permalinks.

## History

- **2026-09-15:** Conjectures.io records Lean verification of JenW1N's submission; its review was approved on 2026-09-16 and certified on 2026-09-17. [Public certificate](https://conjectures.io/results/8186c13b-077f-45bb-8702-870f1dab27e3).
- **2026-10-18:** Recovered the public accepted source unchanged, recorded its checksum and external provenance, and retained local verification as pending. See the [submission audit](../../docs/submission-audit-2026-10-18.md). This history does not record a separate manuscript announcement or JSP submission for Green #40.
