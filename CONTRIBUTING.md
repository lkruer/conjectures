# Adding and updating a proof

[Back to the proof index](README.md#proof-index)

## Start with the manuscript

1. Identify the problem number and its page on [Erdős Problems](https://www.erdosproblems.com/).
2. Copy the complete `templates/problem/` folder to `problems/erdos-<number>/`. Use the number without leading zeros.
3. Replace `{{NUMBER}}` and `{{TITLE}}` in the copied files. Fill in the official problem link, authors, exact statement, scope, and current review status. Replace the template instruction block with a short abstract.
4. Add the supplied PDF as `paper/proof.pdf`. Preserve the manuscript's contents and author line. Optional source files belong alongside it; keep their original internal structure.
5. Change the manuscript row in the problem README to `[Read the proof](paper/proof.pdf)` and update `paper/README.md` to describe the uploaded files. Link only files that exist. Fill in the version or date printed in the manuscript; use “not specified” if absent.
6. Replace the empty-state row and introductory sentence in the root proof index with a real entry, sorted by numeric problem number. Update `problems/README.md` to remove its empty-state note. Link the problem folder and the PDF. Leave Lean as “Not uploaded” until files arrive and submission as “Draft” until its status changes.

A PDF can be published in the repository while review or formalization is still in progress. Record that state on the problem page.

## Add the Lean project when available

Place the supplied sources in the same problem's `lean/` folder. Preserve module names, imports, and project structure. Include the original `lean-toolchain`, `lakefile.toml` or `lakefile.lean`, and `lake-manifest.json` when available. If only standalone `.lean` files are supplied, record the missing configuration before attempting to reproduce the project.

Use the [Lean verification guide](docs/lean-verification.md), then update the build record in that problem's `lean/README.md`. Set the index to “Uploaded; not checked” until verification has actually run. Keep different problems' Lean environments independent so a later upload can retain its original dependency versions.

## Revise or submit

- Keep the current manuscript at `paper/proof.pdf` and record material changes in the problem README's revision notes.
- Let Git history preserve earlier versions. Retain original source filenames when they are needed for compilation.
- For a submission, use links containing a full commit SHA so the reviewed version stays identifiable. Record that SHA and the exact links in `submission.md`.
- Follow the [submission guide](docs/submission-guide.md) before changing the status to “Ready to submit”. Record any actual announcement and subsequent feedback separately.

## Review feedback

Repository issues can be used for feedback. Include the problem number, the PDF revision and page or theorem number, or the Lean file and declaration. Describe the gap, correction, or reproduction failure precisely enough to investigate.
