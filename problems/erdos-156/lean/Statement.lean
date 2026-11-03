import Mathlib

/-!
Definitions transcribed from Formal Conjectures, retaining the standard
Sidon convention including diagonal sums. No theorem or axiom is assumed.
Original question: https://www.erdosproblems.com/156
-/

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

theorem IsSidon.subset {α : Type*} [AddCommMonoid α] {A B : Set α}
    (hB : IsSidon B) (hAB : A ⊆ B) : IsSidon A :=
  fun _ hi _ hj _ hk _ hl h => hB _ (hAB hi) _ (hAB hj) _ (hAB hk) _ (hAB hl) h

def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ ⦃x : ℕ⦄, x ∈ Set.Icc 1 N → x ∉ A → ¬ IsSidon (A ∪ {x})

end Set

namespace Erdos156

open Finset Filter

noncomputable def minMaximalSidonSet (N : ℕ) : ℕ :=
  open scoped Classical in
  sInf (((Icc 1 N).powerset.filter fun (A : Finset ℕ) ↦
    Set.IsMaximalSidonSetIn (A : Set ℕ) N).image card : Set ℕ)

abbrev Target : Prop := True ↔
  (fun N ↦ (minMaximalSidonSet N : ℝ)) =O[atTop]
    (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ))

end Erdos156
