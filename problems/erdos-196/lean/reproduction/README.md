# Erdős 196: reproducible Lean submission

Submitted mathematical solution and Lean proof by **Jensen Kohlmeyer (`jenw1n`) and Liam Kruer (`lkruer`)**.

The supplied construction gives a bijection of all natural numbers with no increasing or decreasing four-term arithmetic progression as a subsequence.

From this directory, run:

```sh
python3 scripts/reproduce.py
```

See [the full reproduction instructions](REPRODUCING.md), [verification record](VERIFICATION.md), [audit output](verification/audit.log), and [third-party notices](THIRD_PARTY_NOTICES.md).

The original clean payload is preserved in `originals/Erdos196-submission.lean`. `Erdos196.lean` adds the required import/namespace wrapper. `PaperMain.lean` is a newly checked short corollary presenting the manuscript's statement directly; it does not replace or repair the original construction.
