# Third-party materials

`TaskSupport.lean` is copied without modification from [conjectures-io/conjectures-validator, commit c36660f7ddd212eb5d253853adb92b928dcb0581](https://github.com/conjectures-io/conjectures-validator/blob/c36660f7ddd212eb5d253853adb92b928dcb0581/lean/TaskSupport.lean). The same commit's [pyproject.toml](https://github.com/conjectures-io/conjectures-validator/blob/c36660f7ddd212eb5d253853adb92b928dcb0581/pyproject.toml) declares `license = { text = "Apache-2.0" }`. The Apache 2.0 license text is included in `licenses/Apache-2.0.txt`.

The Formal Conjectures patch and commit metadata preserve changes by the Conjectures Pool Builder to the Formal Conjectures Authors' Apache 2.0 source. `scripts/bootstrap.py` reconstructs that exact dependency from the official base without changing the submitted mathematical argument. Formal Conjectures' copyright notices remain in the reconstructed source.

Mathlib and its dependencies are fetched at the revisions in `lake-manifest.json`; their original notices and licenses remain in their dependency checkouts. These third-party dependency authors are not being presented as authors of the submitted Erdős 196 solution.
