import Main

open Filter

namespace IndependentAudit

/-- Direct formulation with all interval, Sidon and maximality conditions expanded. -/
theorem original_question :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧
      (∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
        i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ∧
      (∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ A →
        ¬ (∀ i₁ ∈ (A : Set ℕ) ∪ {x}, ∀ j₁ ∈ (A : Set ℕ) ∪ {x},
          ∀ i₂ ∈ (A : Set ℕ) ∪ {x}, ∀ j₂ ∈ (A : Set ℕ) ∪ {x},
          i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁))) ∧
      (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, h⟩ := Bounty.Construction.eventual_small_maximal_sets
  refine ⟨C, hC, h.mono ?_⟩
  intro N hN
  obtain ⟨A, hA, hbound⟩ := hN
  refine ⟨A, ?_, hA.2.1, ?_, hbound⟩
  · intro x hx
    exact hA.1 hx
  · intro x hx1 hxN hxA
    exact hA.2.2 ⟨hx1, hxN⟩ hxA

end IndependentAudit

#check @Bounty.target
#check @Erdos156.solved
#check @IndependentAudit.original_question
#print axioms Bounty.target
#print axioms Erdos156.solved
#print axioms Bounty.target_iff_small_maximal_sets
#print axioms Bounty.Construction.eventual_small_maximal_sets
#print axioms IndependentAudit.original_question
#print Erdos156.solved
