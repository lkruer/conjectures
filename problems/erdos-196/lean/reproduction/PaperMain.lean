import Erdos196

/-! A direct restatement of manuscript Theorem 1.1 using the supplied proof. -/

namespace Bounty

/-- The manuscript's bijection, with no four indexed values in arithmetic progression. -/
theorem paper_main : ∃ p : ℕ ≃ ℕ, ∀ i j k l : ℕ,
    i < j → j < k → k < l →
    ¬ (p i + p k = 2 * p j ∧ p j + p l = 2 * p k) := by
  refine ⟨Equiv.ofBijective Construction196.permFun
    ⟨Construction196.permFun_injective, Construction196.permFun_surjective⟩, ?_⟩
  intro i j k l hij hjk hkl h
  exact Construction196.permFun_no_four i j k l hij hjk hkl h.1 h.2

end Bounty
