# Submission — Erdős 196 / JSP-000185

**Status: [JSP submission 4875](https://github.com/TheJustinSunPrize/awards/pull/4875) pending review; new verification and September 9 completion evidence supplied.**

The submitted construction and formalization are credited to Jensen Kohlmeyer ([jenw1n](https://github.com/JENW1N)) and Liam Kruer ([lkruer](https://github.com/lkruer)). The [original seven-page manuscript](paper/proof.pdf), dated September 9, 2026, and [original Lean payload](lean/Erdos196.lean) are preserved. The [reproduction package](lean/reproduction/README.md) supplies the complete wrapped proof, pinned dependencies, commands and fresh verification evidence.

The manuscript's Theorem 1.1 gives a bijection of all natural numbers avoiding increasing and decreasing four-term arithmetic progressions as subsequences. Sections 2–5 establish the finite extension construction, and Section 6 derives the infinite permutation. The formal target is `Bounty.Construction196.counterexample`, together with the exact catalogue-negation theorem `Bounty.target`.

The [October 10 verification report and logs](verification/2026-10-10/report.md) record the new source and independent checks. The [priority statement](PRIORITY.md) claims completion by the external service's September 9 verification and supplies an executable connection to the identical accepted source.

## Existing publication

- Original repository upload: [commit 8ede860e8fc90a300207a2c17e8aefe6167b3086](https://github.com/lkruer/conjectures/commit/8ede860e8fc90a300207a2c17e8aefe6167b3086), recorded September 14, 2026.
- Public author claim: [Erdős Problems claim 311](https://www.erdosproblems.com/forum/thread/196/proof-claims#proof-claim-311), displayed September 14, 2026.
- Earlier public result disclosed: Boon Suan Ho's [arXiv:2609.12780v1](https://arxiv.org/abs/2609.12780v1), submitted September 11, 2026.

The manuscript date alone does not establish public priority. See the [full history and attribution record](PUBLICATION-HISTORY.md). No first-publication claim or award entitlement is asserted.

## JSP record

The correct catalogue entry is [JSP-000185](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000185). The contribution is submitted through the original repository owner's connected `lkruer` account, crediting both authors. It is a reference-only mathematical and Lean submission; proof files remain in this repository.

The selected proof commit is `bf058b903350eb8f873a22ab4a54b2e0faa9727d`, on `jsp-000185-erdos196`; the existing PR is [4875](https://github.com/TheJustinSunPrize/awards/pull/4875). Later evidence publication preserves the selected proof source. A pending PR does not establish JSP acceptance or prize eligibility. Each future applicant must follow JSP's own-account claim and identity process if invited or eligible; this submission does not make proxy prize claims.

## Verification limits

Fresh local verification and the full axiom audit are recorded in the reproduction package. These checks are distinct from independent human mathematical review and from the historical validator assertions in the PDF. The manuscript's acknowledgment of extensive Codex assistance remains intact.
