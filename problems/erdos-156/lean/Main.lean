import Erdos156

open Filter

/-- The affirmative answer, without the challenge's `True ↔` wrapper. -/
theorem Erdos156.solved :
    (fun N ↦ (Erdos156.minMaximalSidonSet N : ℝ)) =O[atTop]
      (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ)) :=
  Bounty.target.mp trivial
