# Adding and updating a proof

[Back to the proof index](README.md#proof-index)

## Start with the manuscript

1. Identify the collection, problem number, and any part or variant. Link the problem on [Erdős Problems](https://www.erdosproblems.com/) or in [Ben Green's open problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), as appropriate.
2. Copy the complete `templates/problem/` folder to `problems/erdos-<number>/` or `problems/green-<number>/`. Use the number without leading zeros. Keep parts of the same problem together in one folder and explain their scope.
3. Replace `{{COLLECTION}}`, `{{NUMBER}}`, and `{{TITLE}}` in the copied files. Fill in the problem source link, authors, exact statement, scope, and current review status. Replace the template instruction block with a short abstract.
4. Add the supplied PDF as `paper/proof.pdf`. Preserve the manuscript's contents and author line. Optional source files belong alongside it; keep their original internal structure.
5. Change the manuscript row in the problem README to `[Read the proof](paper/proof.pdf)` and update `paper/README.md` to describe the uploaded files. Link only files that exist. Fill in the version or date printed in the manuscript; use “not specified” if absent.
6. Add or update the root proof-index entry, sorted by number within each collection. Update the counts, `problems/README.md`, and `docs/upload-inventory.md` when the available files change. Link the problem folder and PDF. Leave Lean as “Not uploaded” until files arrive and submission as “Draft” until its status changes. Record original filenames and refresh the problem’s `SHA256SUMS` when replacing source files.

A PDF can be published in the repository while review or formalization is still in progress. Record that state on the problem page.

## Add the Lean project when available

Place the supplied sources in the same problem's `lean/` folder. Preserve module names, imports, and project structure. Include the original `lean-toolchain`, `lakefile.toml` or `lakefile.lean`, and `lake-manifest.json` when available. If only standalone `.lean` files are supplied, record the missing configuration before attempting to reproduce the project.

Use the [Lean verification guide](docs/lean-verification.md), then update the build record in that problem's `lean/README.md`. Set the index to “Uploaded; not checked” until verification has actually run. Keep different problems' Lean environments independent so a later upload can retain its original dependency versions.

## Revise or submit

- Keep the current manuscript at `paper/proof.pdf` and record material changes in the problem README's revision notes.
- Let Git history preserve earlier versions. Retain original source filenames when they are needed for compilation.
- For a submission, use links containing a full commit SHA so the reviewed version stays identifiable. Record that SHA and the exact links in `submission.md`.
- For Erdős Problems, follow the [submission guide](docs/submission-guide.md) before changing the status to “Ready to submit”. For Green entries, record the intended destination and its guidance in the problem's submission record. Record any actual announcement and subsequent feedback separately.

## Review feedback

Repository issues can be used for feedback. Include the collection and problem number, the PDF revision and page or theorem number, or the Lean file and declaration. Describe the gap, correction, or reproduction failure precisely enough to investigate.
