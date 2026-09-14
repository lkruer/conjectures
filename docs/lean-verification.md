# Recording Lean verification

[Back to the proof index](../README.md#proof-index)

Each problem keeps its own Lean project. Save the supplied toolchain, Lake configuration, dependency manifest, and source files together. Lake uses these to reproduce the environment; see the [Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

## Reproduce the build

From the problem's `lean/` directory, record the Lean version and run the documented build commands. A typical Lake project uses:

```sh
lake env lean --version
lake build
```

Confirm that the build targets include the files containing the claimed result. Record any additional target or file command needed by the supplied project. Keep the supplied manifest when reproducing a version, since changing dependency versions changes what is being checked.

## Record what was checked

Fill in `lean/README.md` with the commit SHA, commands, outcome, relevant warnings, theorem names, and manuscript sections covered. Examine the final theorem's assumptions and axiom dependencies, and record any admitted or unproved steps. Review whether the formal statement matches the stated mathematical result.

Use these labels consistently:

| Lean status | Evidence |
| :--- | :--- |
| Not uploaded | No Lean source files have been supplied. |
| Uploaded; not checked | Sources are present, but no reproduction result is recorded. |
| Incomplete / build failing | Gaps, missing configuration, or build failures are recorded. |
| Build passing; scope recorded | The named targets compile at a recorded revision; coverage, assumptions, and remaining review are documented. |

Update the proof index and problem page after recording the result. Keep mathematical review and submission status in their own fields.
