# Preparing an Erdős Problems submission

[Back to the proof index](../README.md#proof-index)

This guide covers the Erdős Problems website. Green entries have preparation notes and destination records in their own problem folders.

The site’s FAQ directs updates to a comment on the relevant problem or an email identifying the problem. Its forum guidance asks authors to link to an external PDF for long proofs and to understand and check the mathematics before posting. Disclose AI assistance when applicable. Check the current [FAQ](https://www.erdosproblems.com/faq) and [forum guidance](https://www.erdosproblems.com/forum/) before submission.

## Prepare the problem page

Use the problem's README to state the exact result, hypotheses, and any part of the original question left open. Link the manuscript and record its authors and version. Summarize relevant prior work and the outcome of the manuscript review.

When Lean files are included, link the problem's `lean/README.md` verification record and state which part of the manuscript they cover. Use the [verification guide](lean-verification.md) to prepare that record.

## Freeze a reviewable version

Commit the manuscript and available supporting files together. Use the full commit SHA for the links in the announcement; the URLs below are patterns to fill in, not live proof links.

```text
Problem page:
https://github.com/lkruer/conjectures/tree/COMMIT_SHA/problems/erdos-NUMBER

PDF preview:
https://github.com/lkruer/conjectures/blob/COMMIT_SHA/problems/erdos-NUMBER/paper/proof.pdf

Direct PDF:
https://raw.githubusercontent.com/lkruer/conjectures/COMMIT_SHA/problems/erdos-NUMBER/paper/proof.pdf

Lean project, if present:
https://github.com/lkruer/conjectures/tree/COMMIT_SHA/problems/erdos-NUMBER/lean
```

Check that each link opens the intended material. Record the SHA and links in a subsequent update to `submission.md`; the recorded SHA identifies the proof snapshot, so it need not include the later submission record.

## Prepare the announcement

Fill in the problem's `submission.md` with a brief result summary, a PDF link, the scope of any formalization, and acknowledgments or assistance disclosure as applicable. Complete its checklist before setting the status to “Ready to submit”.

After the author posts or sends the announcement, record the date, destination or comment permalink, and proof revision. Set the status to “Submitted”. If the site later references the result, record the relevant page and date before using “Listed on site”. Track corrections and responses in the same submission record.
