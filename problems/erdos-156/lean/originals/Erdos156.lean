import Mathlib
import FormalConjectures.ErdosProblems.«156»
import TaskSupport

/-!
# Erdős problem 156: a small maximal Sidon set

This file proves the Conjectures.io target `Bounty.target` using finite
sign-pattern selection, quadratic Sidon sets, two separated covering alphabets,
periodic tagged anchors, Bertrand's postulate, and maximal completion.

All auxiliary proofs are included below. The only imports are the challenge's
three imports. No additional axioms or admitted proofs are introduced.
-/

namespace Bounty.SignPatterns

open Finset

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module ℝ V]

omit [DecidableEq ι] in
theorem independent_of_all_patterns (f : ι → Module.Dual ℝ V)
    (hpatterns : ∀ S : Finset ι, ∃ x : V, ∀ i, 0 < f i x ↔ i ∈ S) :
    LinearIndependent ℝ f := by
  classical
  have hnonpos : ∀ g : ι → ℝ, ∑ i, g i • f i = 0 → ∀ i, g i ≤ 0 := by
    intro g hg i
    by_contra! hi
    let S := univ.filter fun j => 0 < g j
    obtain ⟨x, hx⟩ := hpatterns S
    have hterms : ∀ j ∈ (univ : Finset ι), 0 ≤ g j * f j x := by
      intro j _
      by_cases hj : 0 < g j
      · exact (mul_pos hj ((hx j).mpr (mem_filter.mpr ⟨mem_univ _, hj⟩))).le
      · have hfx : f j x ≤ 0 := by
          by_contra! hfx
          exact hj (mem_filter.mp ((hx j).mp hfx)).2
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hj) hfx
    have hip : 0 < g i * f i x :=
      mul_pos hi ((hx i).mpr (mem_filter.mpr ⟨mem_univ _, hi⟩))
    have hsum : 0 < ∑ j, g j * f j x :=
      sum_pos' hterms ⟨i, mem_univ _, hip⟩
    have heval := congrArg (fun L : Module.Dual ℝ V => L x) hg
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] at heval
    linarith
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hneg : ∑ j, (-g j) • f j = 0 := by
    have hterm : ∀ j, (-g j) • f j = -(g j • f j) := fun j => neg_smul (g j) (f j)
    simp_rw [hterm]
    rw [sum_neg_distrib, hg, neg_zero]
  have h₁ := hnonpos g hg i
  have h₂ := hnonpos (fun j => -g j) hneg i
  linarith

noncomputable def positiveFamily (f : ι → Module.Dual ℝ V) : Finset (Finset ι) := by
  classical
  exact univ.filter fun S => ∃ x : V, ∀ i, 0 < f i x ↔ i ∈ S

omit [DecidableEq ι] in
theorem mem_positiveFamily {f : ι → Module.Dual ℝ V} {S : Finset ι} :
    S ∈ positiveFamily f ↔ ∃ x : V, ∀ i, 0 < f i x ↔ i ∈ S := by
  classical
  simp [positiveFamily]

theorem independent_of_shattered {f : ι → Module.Dual ℝ V} {S : Finset ι}
    (hS : (positiveFamily f).Shatters S) :
    LinearIndependent ℝ (fun i : S => f i) := by
  classical
  apply independent_of_all_patterns
  intro T
  let T' := T.image (fun i : S => (i : ι))
  have hsub : T' ⊆ S := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact j.property
  obtain ⟨U, hU, heq⟩ := hS hsub
  obtain ⟨x, hx⟩ := mem_positiveFamily.mp hU
  refine ⟨x, fun i => ?_⟩
  have himem : (i : ι) ∈ T' ↔ i ∈ T := by
    simp [T', mem_image]
  have hiU : (i : ι) ∈ U ↔ (i : ι) ∈ T' := by
    have h := congrArg (fun A : Finset ι => (i : ι) ∈ A) heq
    simpa only [mem_inter, i.property, true_and] using Iff.of_eq h
  exact (hx i).trans (hiU.trans himem)

theorem positiveFamily_vcDim_le [Module.Finite ℝ V] (f : ι → Module.Dual ℝ V) :
    (positiveFamily f).vcDim ≤ Module.finrank ℝ V := by
  classical
  apply Finset.sup_le
  intro S hS
  have hi := independent_of_shattered (mem_shatterer.mp hS)
  have hc := hi.fintype_card_le_finrank
  simpa only [Fintype.card_coe, Subspace.dual_finrank_eq] using hc

theorem family_card_le_of_vcDim_le (F : Finset (Finset ι)) {d : ℕ} (hd : F.vcDim ≤ d) :
    F.card ≤ (d + 1) * (Fintype.card ι + 1) ^ d := by
  calc
    F.card ≤ F.shatterer.card := card_le_card_shatterer F
    _ ≤ ∑ k ∈ Iic F.vcDim, (Fintype.card ι).choose k := card_shatterer_le_sum_vcDim
    _ ≤ ∑ _k ∈ Iic F.vcDim, (Fintype.card ι + 1) ^ d := by
      apply sum_le_sum
      intro k hk
      have hkd : k ≤ d := (mem_Iic.mp hk).trans hd
      calc
        (Fintype.card ι).choose k ≤ (Fintype.card ι) ^ k := Nat.choose_le_pow _ _
        _ ≤ (Fintype.card ι + 1) ^ k := Nat.pow_le_pow_left (by omega) k
        _ ≤ (Fintype.card ι + 1) ^ d := Nat.pow_le_pow_right (by omega) hkd
    _ = (F.vcDim + 1) * (Fintype.card ι + 1) ^ d := by simp
    _ ≤ (d + 1) * (Fintype.card ι + 1) ^ d := by gcongr

theorem positiveFamily_card_le [Module.Finite ℝ V] (f : ι → Module.Dual ℝ V) :
    (positiveFamily f).card ≤
      (Module.finrank ℝ V + 1) * (Fintype.card ι + 1) ^ (Module.finrank ℝ V) :=
  family_card_le_of_vcDim_le _ (positiveFamily_vcDim_le f)

noncomputable def positiveSet (f : ι → Module.Dual ℝ V) (x : V) : Finset ι := by
  classical
  exact univ.filter fun i => 0 < f i x

omit [DecidableEq ι] in
theorem positiveSet_mem (f : ι → Module.Dual ℝ V) (x : V) :
    positiveSet f x ∈ positiveFamily f := by
  classical
  apply mem_positiveFamily.mpr
  exact ⟨x, fun i => by simp [positiveSet]⟩

/-- Finite labels determined by signs have a polynomial cardinality bound, including zeros. -/
theorem sign_determined_card_le [Module.Finite ℝ V] {X α : Type*} [DecidableEq α]
    (f : ι → Module.Dual ℝ V) (embed : X → V) (label : X → α) (F : Finset α)
    (hrealize : ∀ a ∈ F, ∃ x : X, label x = a)
    (hdet : ∀ x y, (∀ i,
      (0 < f i (embed x) ↔ 0 < f i (embed y)) ∧
      (f i (embed x) < 0 ↔ f i (embed y) < 0)) → label x = label y) :
    F.card ≤ ((Module.finrank ℝ V + 1) *
      (Fintype.card ι + 1) ^ (Module.finrank ℝ V)) ^ 2 := by
  classical
  let rep (a : F) : X := Classical.choose (hrealize a a.property)
  have hrep (a : F) : label (rep a) = a := Classical.choose_spec (hrealize a a.property)
  let g : F → (positiveFamily f) × (positiveFamily (fun i => -f i)) := fun a =>
    (⟨positiveSet f (embed (rep a)), positiveSet_mem _ _⟩,
      ⟨positiveSet (fun i => -f i) (embed (rep a)), positiveSet_mem _ _⟩)
  have hginj : Function.Injective g := by
    intro a b hab
    have hpos : positiveSet f (embed (rep a)) = positiveSet f (embed (rep b)) :=
      congrArg (fun z : (positiveFamily f) × (positiveFamily (fun i => -f i)) => z.1.val) hab
    have hneg : positiveSet (fun i => -f i) (embed (rep a)) =
        positiveSet (fun i => -f i) (embed (rep b)) :=
      congrArg (fun z : (positiveFamily f) × (positiveFamily (fun i => -f i)) => z.2.val) hab
    apply Subtype.ext
    rw [← hrep a, ← hrep b]
    apply hdet
    intro i
    constructor
    · have h := congrArg (fun S : Finset ι => i ∈ S) hpos
      simpa [positiveSet] using Iff.of_eq h
    · have h := congrArg (fun S : Finset ι => i ∈ S) hneg
      simpa [positiveSet] using Iff.of_eq h
  have hcard : F.card ≤ (positiveFamily f).card * (positiveFamily (fun i => -f i)).card := by
    simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective g hginj
  exact hcard.trans (by
    simpa only [pow_two] using Nat.mul_le_mul (positiveFamily_card_le f)
      (positiveFamily_card_le (fun i => -f i)))

def augmentForm (a : Module.Dual ℝ V) (c : ℝ) : Module.Dual ℝ (ℝ × V) :=
  c • LinearMap.fst ℝ ℝ V + a.comp (LinearMap.snd ℝ ℝ V)

@[simp] theorem augmentForm_apply (a : Module.Dual ℝ V) (c : ℝ) (x : V) :
    augmentForm a c (1, x) = c + a x := by
  simp [augmentForm]

/-- An explicit uniform bound for labels determined by finitely many affine signs. -/
theorem affine_sign_determined_card_le [Module.Finite ℝ V] {X α : Type*} [DecidableEq α]
    (a : ι → Module.Dual ℝ V) (c : ι → ℝ) (embed : X → V) (label : X → α) (F : Finset α)
    (hrealize : ∀ y ∈ F, ∃ x : X, label x = y)
    (hdet : ∀ x y, (∀ i,
      (0 < c i + a i (embed x) ↔ 0 < c i + a i (embed y)) ∧
      (c i + a i (embed x) < 0 ↔ c i + a i (embed y) < 0)) → label x = label y) :
    F.card ≤ ((Module.finrank ℝ V + 2) *
      (Fintype.card ι + 1) ^ (Module.finrank ℝ V + 1)) ^ 2 := by
  have h := sign_determined_card_le (fun i => augmentForm (a i) (c i))
    (fun x => (1, embed x)) label F hrealize (by simpa using hdet)
  simpa [Module.finrank_prod, add_assoc, add_comm, add_left_comm] using h

theorem floor_mem_cut_interval {B : ℕ} {x : ℝ}
    (hx : -(B : ℝ) ≤ x ∧ x ≤ B) : ⌊x⌋ ∈ Icc (-(B : ℤ)) B := by
  apply mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    simpa using hx.1
  · apply Int.floor_le_iff.mpr
    push_cast
    linarith [hx.2]

theorem floor_eq_of_integer_cuts {B : ℕ} {x y : ℝ}
    (hx : -(B : ℝ) ≤ x ∧ x ≤ B) (hy : -(B : ℝ) ≤ y ∧ y ≤ B)
    (hcuts : ∀ k ∈ Icc (-(B : ℤ)) B, (x - k < 0 ↔ y - k < 0)) :
    ⌊x⌋ = ⌊y⌋ := by
  apply le_antisymm
  · apply Int.le_floor.mpr
    have hcut := hcuts ⌊x⌋ (floor_mem_cut_interval hx)
    have hfloor := Int.floor_le x
    by_contra! h
    have hycut : y - (⌊x⌋ : ℝ) < 0 := by linarith
    have := hcut.mpr hycut
    linarith
  · apply Int.le_floor.mpr
    have hcut := hcuts ⌊y⌋ (floor_mem_cut_interval hy)
    have hfloor := Int.floor_le y
    by_contra! h
    have hxcut : x - (⌊y⌋ : ℝ) < 0 := by linarith
    have := hcut.mp hxcut
    linarith

theorem fract_lt_iff_of_integer_cuts {B : ℕ} {x y u v : ℝ}
    (hx : -(B : ℝ) ≤ x ∧ x ≤ B) (hy : -(B : ℝ) ≤ y ∧ y ≤ B)
    (hcuts : ∀ k ∈ Icc (-(B : ℤ)) B, (x - k < 0 ↔ y - k < 0))
    (hcomp : ∀ k ∈ Icc (-(B : ℤ)) B, (x - u - k < 0 ↔ y - v - k < 0)) :
    Int.fract x < u ↔ Int.fract y < v := by
  have hfloor := floor_eq_of_integer_cuts hx hy hcuts
  have h := hcomp ⌊x⌋ (floor_mem_cut_interval hx)
  change x - (⌊x⌋ : ℝ) < u ↔ y - (⌊y⌋ : ℝ) < v
  rw [← hfloor]
  constructor
  · intro hx'
    have hx'' : x - u - (⌊x⌋ : ℝ) < 0 := by linarith
    have hy' := h.mp hx''
    linarith
  · intro hy'
    have hy'' : y - v - (⌊x⌋ : ℝ) < 0 := by linarith
    have hx' := h.mpr hy''
    linarith

/-- Fractional affine phases with a bounded range still have polynomially many labels. -/
theorem fractional_phase_card_le [Module.Finite ℝ V] {X α : Type*} [DecidableEq α]
    (f g : ι → Module.Dual ℝ V) (cf cg : ι → ℝ)
    (embed : X → V) (label : X → α) (F : Finset α) (B : ℕ)
    (hbound : ∀ x i, -(B : ℝ) ≤ cf i + f i (embed x) ∧ cf i + f i (embed x) ≤ B)
    (hrealize : ∀ y ∈ F, ∃ x : X, label x = y)
    (hdet : ∀ x y, (∀ i,
      (Int.fract (cf i + f i (embed x)) < cg i + g i (embed x) ↔
       Int.fract (cf i + f i (embed y)) < cg i + g i (embed y))) → label x = label y) :
    F.card ≤ ((Module.finrank ℝ V + 2) *
      (2 * Fintype.card ι * (2 * B + 1) + 1) ^ (Module.finrank ℝ V + 1)) ^ 2 := by
  classical
  let J := Bool × ι × ↥(Icc (-(B : ℤ)) B)
  let af : J → Module.Dual ℝ V := fun j => if j.1 then f j.2.1 - g j.2.1 else f j.2.1
  let ac : J → ℝ := fun j =>
    if j.1 then cf j.2.1 - cg j.2.1 - (j.2.2 : ℤ) else cf j.2.1 - (j.2.2 : ℤ)
  have hdet' : ∀ x y, (∀ j : J,
      (0 < ac j + af j (embed x) ↔ 0 < ac j + af j (embed y)) ∧
      (ac j + af j (embed x) < 0 ↔ ac j + af j (embed y) < 0)) → label x = label y := by
    intro x y hsign
    apply hdet
    intro i
    apply fract_lt_iff_of_integer_cuts (hbound x i) (hbound y i)
    · intro k hk
      have h := (hsign (false, i, ⟨k, hk⟩)).2
      simp only [af, ac, Bool.false_eq_true, ite_false] at h
      constructor
      · intro h'
        have hh := h.mp (by linarith)
        linarith
      · intro h'
        have hh := h.mpr (by linarith)
        linarith
    · intro k hk
      have h := (hsign (true, i, ⟨k, hk⟩)).2
      simp only [af, ac, ite_true, LinearMap.sub_apply] at h
      constructor
      · intro h'
        have hh := h.mp (by linarith)
        linarith
      · intro h'
        have hh := h.mpr (by linarith)
        linarith
  have hc := affine_sign_determined_card_le af ac embed label F hrealize hdet'
  have hcutcard : Fintype.card ↥(Icc (-(B : ℤ)) B) = 2 * B + 1 := by
    rw [Fintype.card_coe, Int.card_Icc]
    omega
  have hJ : Fintype.card J = 2 * Fintype.card ι * (2 * B + 1) := by
    simp [J, hcutcard, mul_assoc]
  simpa only [hJ] using hc

end Bounty.SignPatterns


namespace Bounty

open Finset Filter

/-- Finite union-bound form of the manuscript's random-word argument. -/
theorem exists_hitting_word {m b : ℕ} (patterns : Finset (Fin m → Finset (Fin b)))
    (hne : ∀ G ∈ patterns, ∀ i, (G i).Nonempty)
    (hsize : patterns.card * (b - 1) ^ m < b ^ m) :
    ∃ w : Fin m → Fin b, ∀ G ∈ patterns, ∃ i, w i ∈ G i := by
  classical
  let bad (G : Fin m → Finset (Fin b)) : Finset (Fin m → Fin b) :=
    Fintype.piFinset fun i => univ \ G i
  have hbad (G) (hG : G ∈ patterns) : (bad G).card ≤ (b - 1) ^ m := by
    rw [Fintype.card_piFinset]
    calc
      _ ≤ ∏ _ : Fin m, (b - 1) := by
        apply Finset.prod_le_prod
        intro i _
        have hi : 1 ≤ (G i).card := card_pos.mpr (hne G hG i)
        simp only [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
        omega
      _ = (b - 1) ^ m := by simp
  let excluded := patterns.biUnion bad
  have hexcluded : excluded.card < Fintype.card (Fin m → Fin b) := by
    calc
      excluded.card ≤ ∑ G ∈ patterns, (bad G).card := card_biUnion_le
      _ ≤ ∑ _G ∈ patterns, (b - 1) ^ m := sum_le_sum hbad
      _ = patterns.card * (b - 1) ^ m := by simp
      _ < b ^ m := hsize
      _ = Fintype.card (Fin m → Fin b) := by simp
  have houtside : ∃ w : Fin m → Fin b, w ∉ excluded := by
    by_contra! h
    have hu : (univ : Finset (Fin m → Fin b)) ⊆ excluded := fun w _ => h w
    have := card_le_card hu
    simp only [card_univ] at this
    omega
  obtain ⟨w, hw⟩ := houtside
  refine ⟨w, ?_⟩
  intro G hG
  by_contra! h
  apply hw
  apply mem_biUnion.mpr
  refine ⟨G, hG, Fintype.mem_piFinset.mpr ?_⟩
  intro i
  exact mem_sdiff.mpr ⟨mem_univ _, h i⟩

/-- One word can hit every pattern under each member of a finite set of permutations. -/
theorem exists_hitting_word_permutations {m b : ℕ}
    (patterns : Finset (Fin m → Finset (Fin b))) (perms : Finset (Equiv.Perm (Fin m)))
    (hne : ∀ G ∈ patterns, ∀ i, (G i).Nonempty)
    (hsize : perms.card * patterns.card * (b - 1) ^ m < b ^ m) :
    ∃ w : Fin m → Fin b, ∀ e ∈ perms, ∀ G ∈ patterns, ∃ i, w (e i) ∈ G i := by
  classical
  let transformed := (perms ×ˢ patterns).image fun (e, G) i => G (e.symm i)
  have hnonempty : ∀ G ∈ transformed, ∀ i, (G i).Nonempty := by
    intro G hG i
    obtain ⟨⟨e, H⟩, hEH, rfl⟩ := mem_image.mp hG
    exact hne H (mem_product.mp hEH).2 (e.symm i)
  have hcard : transformed.card ≤ perms.card * patterns.card := by
    exact (card_image_le).trans_eq (card_product _ _)
  obtain ⟨w, hw⟩ := exists_hitting_word transformed hnonempty
    (lt_of_le_of_lt (Nat.mul_le_mul_right ((b - 1) ^ m) hcard) hsize)
  refine ⟨w, ?_⟩
  intro e he G hG
  have hmem : (fun i => G (e.symm i)) ∈ transformed :=
    mem_image.mpr ⟨(e, G), mem_product.mpr ⟨he, hG⟩, rfl⟩
  obtain ⟨i, hi⟩ := hw _ hmem
  exact ⟨e.symm i, by simpa using hi⟩

/-- Every fixed polynomial times `(b - 1)^m` is eventually smaller than `b^m`. -/
theorem polynomial_geometric_eventually_lt (A B b : ℕ) (hb : 1 < b) :
    ∀ᶠ m : ℕ in atTop, A * m ^ B * (b - 1) ^ m < b ^ m := by
  have hnorm : ‖((b - 1 : ℕ) : ℝ)‖ < (b : ℝ) := by
    rw [Real.norm_natCast]
    exact_mod_cast (by omega : b - 1 < b)
  have hsmall :=
    (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) B hnorm).const_mul_left
      (A : ℝ)
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound] with m hm
  have hle : ((A * m ^ B * (b - 1) ^ m : ℕ) : ℝ) ≤ 1 / 2 * (b : ℝ) ^ m := by
    simpa [norm_mul, norm_pow, Real.norm_natCast, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hm
  have hpos : (0 : ℝ) < (b : ℝ) ^ m := by
    apply pow_pos
    exact_mod_cast (by omega : 0 < b)
  have hlt : ((A * m ^ B * (b - 1) ^ m : ℕ) : ℝ) < (b : ℝ) ^ m := by linarith
  exact_mod_cast hlt

/-- Polynomially many nonempty choice matrices admit a common hitting word. -/
theorem exists_hitting_word_of_polynomial_bound {A B b : ℕ} (hb : 1 < b)
    (patterns : (m : ℕ) → Finset (Fin m → Finset (Fin b)))
    (hne : ∀ m, ∀ G ∈ patterns m, ∀ i, (G i).Nonempty)
    (hcard : ∀ m, (patterns m).card ≤ A * m ^ B) (lower : ℕ) :
    ∃ m ≥ lower, ∃ w : Fin m → Fin b, ∀ G ∈ patterns m, ∃ i, w i ∈ G i := by
  obtain ⟨m, hm, hlower⟩ :=
    ((polynomial_geometric_eventually_lt A B b hb).and (eventually_ge_atTop lower)).exists
  refine ⟨m, hlower, exists_hitting_word (patterns m) (hne m) ?_⟩
  exact lt_of_le_of_lt (Nat.mul_le_mul_right ((b - 1) ^ m) (hcard m)) hm

private theorem pair_of_sum_sq {F : Type*} [Field F] {x y z w : F}
    (h2 : (2 : F) ≠ 0) (hs : x + y = z + w)
    (hq : x ^ 2 + y ^ 2 = z ^ 2 + w ^ 2) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have hp : x * y = z * w := by
    apply mul_left_cancel₀ h2
    linear_combination (x + y + z + w) * hs - hq
  have hr : (x - z) * (x - w) = 0 := by
    linear_combination x * hs - hp
  rcases mul_eq_zero.mp hr with h | h
  · left
    have hx := sub_eq_zero.mp h
    exact ⟨hx, add_left_cancel (hx ▸ hs)⟩
  · right
    have hx := sub_eq_zero.mp h
    refine ⟨hx, ?_⟩
    rw [hx, add_comm z w] at hs
    exact add_left_cancel hs

/-- The integer representative used for the manuscript's quadratic seed. -/
def quadraticMark (p t : ℕ) : ℕ := t + 2 * p * (t ^ 2 % p)

/-- The seed has one mark for every residue modulo `p`. -/
def quadraticSeed (p : ℕ) : Finset ℕ := (range p).image (quadraticMark p)

private theorem quadraticMark_mod (p t : ℕ) :
    quadraticMark p t % (2 * p) = t % (2 * p) := by
  simp [quadraticMark, Nat.add_mod]

/-- Equality of seed pair sums determines the unordered pair of parameters. -/
theorem quadraticMark_pair {p i j k l : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hi : i < p) (hj : j < p) (hk : k < p) (hl : l < p)
    (h : quadraticMark p i + quadraticMark p j =
      quadraticMark p k + quadraticMark p l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hsum : i + j = k + l := by
    have hm := congrArg (fun n : ℕ => n % (2 * p)) h
    have hpair (a b : ℕ) : (quadraticMark p a + quadraticMark p b) % (2 * p) =
        (a + b) % (2 * p) := by
      calc
        _ = (quadraticMark p a % (2 * p) + quadraticMark p b % (2 * p)) %
            (2 * p) := Nat.add_mod _ _ _
        _ = (a % (2 * p) + b % (2 * p)) % (2 * p) := by
          rw [quadraticMark_mod, quadraticMark_mod]
        _ = (a + b) % (2 * p) := (Nat.add_mod _ _ _).symm
    have hm' : (i + j) % (2 * p) = (k + l) % (2 * p) := by
      rwa [hpair, hpair] at hm
    rwa [Nat.mod_eq_of_lt (by omega : i + j < 2 * p),
      Nat.mod_eq_of_lt (by omega : k + l < 2 * p)] at hm'
  have hres : i ^ 2 % p + j ^ 2 % p = k ^ 2 % p + l ^ 2 % p := by
    have hpos := hp.pos
    dsimp [quadraticMark] at h
    nlinarith
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro heq
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp heq
    have := (Nat.dvd_prime Nat.prime_two).mp hd
    rcases this with h | h
    · exact hp.ne_one h
    · exact hodd h
  have hs : (i : ZMod p) + j = (k : ZMod p) + l := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) hsum
  have hq : (i : ZMod p) ^ 2 + (j : ZMod p) ^ 2 =
      (k : ZMod p) ^ 2 + (l : ZMod p) ^ 2 := by
    have heq := congrArg (fun n : ℕ => (n : ZMod p)) hres
    simpa using heq
  have hinj : ∀ {a b : ℕ}, a < p → b < p →
      (a : ZMod p) = b → a = b := by
    intro a b ha hb hab
    have heq := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq
  rcases pair_of_sum_sq htwo hs hq with h | h
  · exact Or.inl ⟨hinj hi hk h.1, hinj hj hl h.2⟩
  · exact Or.inr ⟨hinj hi hl h.1, hinj hj hk h.2⟩

/-- A field difference lifts to an actual integer difference with two binary carries. -/
theorem quadratic_difference_lift {p d H : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) (hH0 : 0 < H) (hHp : H < p) :
    ∃ t < p, ∃ u < p, ∃ σ : ℕ, σ ≤ 1 ∧ ∃ ε : ℕ, ε ≤ 1 ∧
      (quadraticMark p t : ℤ) - quadraticMark p u =
        d - (p : ℤ) * σ + 2 * p * H - 2 * (p : ℤ) ^ 2 * ε := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro heq
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp heq
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact hp.ne_one h
    · exact hodd h
  have hd : (d : ZMod p) ≠ 0 := by
    intro heq
    have hm := (ZMod.natCast_eq_natCast_iff' d 0 p).mp (by simpa using heq)
    simp only [Nat.mod_eq_of_lt hdp, Nat.zero_mod] at hm
    omega
  have hden : (2 * (d : ZMod p)) ≠ 0 := mul_ne_zero htwo hd
  let t := (((H : ZMod p) + (d : ZMod p) ^ 2) / (2 * d)).val
  have ht : t < p := ZMod.val_lt _
  have htf : (t : ZMod p) = ((H : ZMod p) + (d : ZMod p) ^ 2) / (2 * d) :=
    ZMod.natCast_zmod_val _
  have hlin : 2 * (d : ZMod p) * t = H + (d : ZMod p) ^ 2 := by
    rw [htf]
    field_simp
  let σ : ℕ := if d ≤ t then 0 else 1
  let u : ℕ := if d ≤ t then t - d else t + p - d
  have hσ : σ ≤ 1 := by dsimp [σ]; split_ifs <;> omega
  have hu : u < p := by dsimp [u]; split_ifs <;> omega
  have husum : u + d = t + p * σ := by
    dsimp [u, σ]
    split_ifs <;> simp <;> omega
  have hsub : (t : ℤ) - u = d - (p : ℤ) * σ := by
    have hz : (u : ℤ) + d = t + (p : ℤ) * σ := by exact_mod_cast husum
    omega
  have huf : (u : ZMod p) = (t : ZMod p) - d := by
    apply eq_sub_of_add_eq
    have hz := congrArg (fun n : ℕ => (n : ZMod p)) husum
    simpa using hz
  have hq : (t : ZMod p) ^ 2 - (u : ZMod p) ^ 2 = H := by
    rw [huf]
    linear_combination hlin
  have hdiv : (p : ℤ) ∣ ((t ^ 2 % p : ℕ) : ℤ) - (u ^ 2 % p : ℕ) - H := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    simpa using sub_eq_zero.mpr hq
  obtain ⟨z, hz⟩ := hdiv
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have htq0 : (0 : ℤ) ≤ (t ^ 2 % p : ℕ) := Nat.cast_nonneg _
  have huq0 : (0 : ℤ) ≤ (u ^ 2 % p : ℕ) := Nat.cast_nonneg _
  have htq : ((t ^ 2 % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt (t ^ 2) hp.pos
  have huq : ((u ^ 2 % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt (u ^ 2) hp.pos
  have hHz0 : (0 : ℤ) < H := by exact_mod_cast hH0
  have hHzp : (H : ℤ) < p := by exact_mod_cast hHp
  have hzlo : -1 ≤ z := by
    by_contra! h
    have : z ≤ -2 := by omega
    nlinarith
  have hzhi : z ≤ 0 := by
    by_contra! h
    have : 1 ≤ z := h
    nlinarith
  have hzcases : z = -1 ∨ z = 0 := by omega
  refine ⟨t, ht, u, hu, σ, hσ, ?_⟩
  rcases hzcases with rfl | rfl
  · refine ⟨1, by decide, ?_⟩
    simp only [quadraticMark, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one]
    nlinarith
  · refine ⟨0, by decide, ?_⟩
    simp only [quadraticMark, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero,
      sub_zero]
    nlinarith

/-- Six translates already suffice for the local step called the eight-option fact. -/
theorem quadratic_six_option_cover {p d H k τ : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) (hH0 : 0 < H) (hHp : H < p) (hτ : τ ≤ 1) :
    ∃ s : ℕ, s ≤ 2 ∧ ∃ ε : ℕ, ε ≤ 1 ∧ ∃ a ∈ quadraticSeed p,
      ∃ b ∈ quadraticSeed p,
        (d : ℤ) + p * τ + 2 * p * (H + k) =
          a - b + (p : ℤ) * (2 * k + s) + ε * (2 * (p : ℤ) ^ 2) := by
  obtain ⟨t, ht, u, hu, σ, hσ, ε, hε, hid⟩ :=
    quadratic_difference_lift hp hodd hd0 hdp hH0 hHp
  refine ⟨τ + σ, by omega, ε, hε, quadraticMark p t,
    mem_image.mpr ⟨t, mem_range.mpr ht, rfl⟩, quadraticMark p u,
    mem_image.mpr ⟨u, mem_range.mpr hu, rfl⟩, ?_⟩
  push_cast
  nlinarith [hid]

/-- The quadratic seed is a strong Sidon set, including diagonal pair sums. -/
theorem quadraticSeed_isSidon {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    IsSidon (quadraticSeed p : Set ℕ) := by
  intro x hx y hy z hz w hw h
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
  rcases quadraticMark_pair hp hodd (mem_range.mp hi) (mem_range.mp hk)
      (mem_range.mp hj) (mem_range.mp hl) h with h | h
  · exact Or.inl ⟨congrArg (quadraticMark p) h.1, congrArg (quadraticMark p) h.2⟩
  · exact Or.inr ⟨congrArg (quadraticMark p) h.1, congrArg (quadraticMark p) h.2⟩

/-- There are exactly `p` distinct marks in the quadratic seed. -/
theorem quadraticSeed_card (p : ℕ) : (quadraticSeed p).card = p := by
  rw [quadraticSeed, card_image_iff.mpr, card_range]
  intro a ha b hb heq
  have hm := congrArg (fun n : ℕ => n % (2 * p)) heq
  rw [quadraticMark_mod, quadraticMark_mod,
    Nat.mod_eq_of_lt (by have := mem_range.mp ha; omega),
    Nat.mod_eq_of_lt (by have := mem_range.mp hb; omega)] at hm
  exact hm

/-- Every seed mark lies in the manuscript's interval `[0, 2 p²)`. -/
theorem quadraticMark_lt {p t : ℕ} (ht : t < p) : quadraticMark p t < 2 * p ^ 2 := by
  have hp : 0 < p := by omega
  have hq := Nat.mod_lt (t ^ 2) hp
  have hq' : t ^ 2 % p + 1 ≤ p := by omega
  dsimp [quadraticMark]
  nlinarith

/-- Distinct ordered pairs in a Sidon set have distinct nonzero differences. -/
theorem sidon_difference_injective {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    Set.InjOn (fun q : ℕ × ℕ => (q.1 : ℤ) - q.2) (A.offDiag : Set (ℕ × ℕ)) := by
  intro q hq r hr heq
  obtain ⟨hq₁, hq₂, hqne⟩ := mem_offDiag.mp hq
  obtain ⟨hr₁, hr₂, _⟩ := mem_offDiag.mp hr
  change (q.1 : ℤ) - (q.2 : ℤ) = (r.1 : ℤ) - (r.2 : ℤ) at heq
  have hsum : q.1 + r.2 = r.1 + q.2 := by omega
  rcases hA q.1 hq₁ r.1 hr₁ r.2 hr₂ q.2 hq₂ hsum with h | h
  · exact Prod.ext h.1 h.2.symm
  · exact (hqne h.1).elim

/-- A cardinality bound obtained by counting differences in an interval. -/
theorem sidon_interval_count {A : Finset ℕ} {u L : ℕ}
    (hA : IsSidon (A : Set ℕ))
    (hinterval : ∀ x ∈ A, u ≤ x ∧ x ≤ u + L) :
    A.card * A.card - A.card ≤ 2 * L + 1 := by
  let differences := A.offDiag.image fun q : ℕ × ℕ => (q.1 : ℤ) - q.2
  have hcard : differences.card = A.offDiag.card :=
    card_image_iff.mpr (sidon_difference_injective hA)
  have hsub : differences ⊆ Icc (-(L : ℤ)) L := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    have hq₁ := hinterval q.1 (mem_offDiag.mp hq).1
    have hq₂ := hinterval q.2 (mem_offDiag.mp hq).2.1
    apply mem_Icc.mpr
    constructor <;> omega
  have hlength : (Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  have hc := card_le_card hsub
  rwa [hcard, offDiag_card, hlength] at hc

/-- An interval of diameter at most `10 p²` contains at most `5 p` Sidon marks. -/
theorem sidon_interval_count_five_mul {A : Finset ℕ} {u L p : ℕ}
    (hp : 1 ≤ p) (hL : L ≤ 10 * p ^ 2) (hA : IsSidon (A : Set ℕ))
    (hinterval : ∀ x ∈ A, u ≤ x ∧ x ≤ u + L) : A.card ≤ 5 * p := by
  have hc := sidon_interval_count hA hinterval
  by_contra! hgt
  have hlow : 5 * p + 1 ≤ A.card := hgt
  have hprod : (5 * p + 1) * (5 * p) ≤ A.card * (A.card - 1) :=
    Nat.mul_le_mul hlow (by omega)
  rw [Nat.mul_sub_left_distrib, mul_one] at hprod
  nlinarith

/-- At most `2 p` marks can lie among multiples of `p` when `N / p ≤ p²`. -/
theorem sidon_multiples_count {A : Finset ℕ} {N p : ℕ}
    (hp : 1 ≤ p) (hN : N / p ≤ p ^ 2) (hA : IsSidon (A : Set ℕ))
    (hdiv : ∀ x ∈ A, p ∣ x) (hbound : ∀ x ∈ A, x ≤ N) : A.card ≤ 2 * p := by
  let U := A.image fun x => x / p
  have hcard : U.card = A.card := by
    apply card_image_iff.mpr
    intro x hx y hy heq
    calc
      x = p * (x / p) := (Nat.mul_div_cancel' (hdiv x hx)).symm
      _ = p * (y / p) := congrArg (fun n => p * n) heq
      _ = y := Nat.mul_div_cancel' (hdiv y hy)
  have hU : IsSidon (U : Set ℕ) := by
    intro a ha b hb c hc d hd heq
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hc
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hd
    have hmul := congrArg (fun n => p * n) heq
    simp only [Nat.mul_add, Nat.mul_div_cancel' (hdiv x hx),
      Nat.mul_div_cancel' (hdiv y hy), Nat.mul_div_cancel' (hdiv z hz),
      Nat.mul_div_cancel' (hdiv w hw)] at hmul
    rcases hA x hx y hy z hz w hw hmul with h | h
    · exact Or.inl ⟨congrArg (fun n => n / p) h.1, congrArg (fun n => n / p) h.2⟩
    · exact Or.inr ⟨congrArg (fun n => n / p) h.1, congrArg (fun n => n / p) h.2⟩
  have hUbound : ∀ q ∈ U, 0 ≤ q ∧ q ≤ 0 + p ^ 2 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
    refine ⟨Nat.zero_le _, ?_⟩
    simpa only [zero_add] using (Nat.div_le_div_right (hbound x hx)).trans hN
  have hc := sidon_interval_count hU hUbound
  rw [← hcard]
  by_contra! hgt
  have hlow : 2 * p + 1 ≤ U.card := hgt
  have hprod : (2 * p + 1) * (2 * p) ≤ U.card * (U.card - 1) :=
    Nat.mul_le_mul hlow (by omega)
  rw [Nat.mul_sub_left_distrib, mul_one] at hprod
  nlinarith

/-- Every Sidon seed in the finite host has a maximal Sidon completion. -/
theorem exists_maximal_completion {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Icc 1 N) (hs : IsSidon (S : Set ℕ)) :
    ∃ A : Finset ℕ, S ⊆ A ∧ Set.IsMaximalSidonSetIn (A : Set ℕ) N := by
  classical
  let candidates := (Icc 1 N).powerset.filter fun A : Finset ℕ =>
    S ⊆ A ∧ IsSidon (A : Set ℕ)
  have hmem : S ∈ candidates := by simp [candidates, hS, hs]
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image card ⟨S, hmem⟩
  have hparts : A ⊆ Icc 1 N ∧ S ⊆ A ∧ IsSidon (A : Set ℕ) := by
    simpa [candidates] using hA
  refine ⟨A, hparts.2.1, ?_, hparts.2.2, ?_⟩
  · intro x hx
    exact mem_Icc.mp (hparts.1 hx)
  · intro x hx hxA hinsert
    have hxA' : x ∉ A := hxA
    have hcand : insert x A ∈ candidates := by
      simp only [candidates, mem_filter, mem_powerset]
      refine ⟨insert_subset (mem_Icc.mpr hx) hparts.1,
        hparts.2.1.trans (subset_insert x A), ?_⟩
      simpa only [coe_insert, Set.insert_eq, Set.union_comm] using hinsert
    have hcard := hmax (insert x A) hcand
    simp [card_insert_of_notMem hxA'] at hcard

/-- A completion only adds unblocked points; three exception bounds control its size. -/
theorem exists_maximal_completion_with_exception_bounds
    {N b₁ b₂ b₃ : ℕ} {S E₁ E₂ E₃ : Finset ℕ}
    (hS : S ⊆ Icc 1 N) (hs : IsSidon (S : Set ℕ))
    (hblocked : ∀ x ∈ Icc 1 N, x ∉ S → x ∉ E₁ → x ∉ E₂ → x ∉ E₃ →
      ¬ IsSidon ((S : Set ℕ) ∪ {x}))
    (h₁ : ∀ T : Finset ℕ, T ⊆ E₁ → IsSidon (T : Set ℕ) → T.card ≤ b₁)
    (h₂ : ∀ T : Finset ℕ, T ⊆ E₂ → IsSidon (T : Set ℕ) → T.card ≤ b₂)
    (h₃ : ∀ T : Finset ℕ, T ⊆ E₃ → IsSidon (T : Set ℕ) → T.card ≤ b₃) :
    ∃ A : Finset ℕ, S ⊆ A ∧ Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧
      A.card ≤ S.card + b₁ + b₂ + b₃ := by
  obtain ⟨A, hSA, hA⟩ := exists_maximal_completion hS hs
  have hcover : ∀ x ∈ A, x ∈ S ∨ x ∈ E₁ ∨ x ∈ E₂ ∨ x ∈ E₃ := by
    intro x hx
    by_contra! h
    apply hblocked x (mem_Icc.mpr (hA.1 hx)) h.1 h.2.1 h.2.2.1 h.2.2.2
    apply Set.IsSidon.subset hA.2.1
    intro y hy
    rcases hy with hy | hy
    · exact hSA hy
    · have hxy : y = x := Set.mem_singleton_iff.mp hy
      simpa [hxy] using hx
  have hsub : A ⊆ S ∪ (A ∩ E₁) ∪ (A ∩ E₂) ∪ (A ∩ E₃) := by
    intro x hx
    rcases hcover x hx with h | h | h | h <;> simp [hx, h]
  have hb₁ : (A ∩ E₁).card ≤ b₁ :=
    h₁ _ inter_subset_right (Set.IsSidon.subset hA.2.1 (by intro x hx; exact (mem_inter.mp hx).1))
  have hb₂ : (A ∩ E₂).card ≤ b₂ :=
    h₂ _ inter_subset_right (Set.IsSidon.subset hA.2.1 (by intro x hx; exact (mem_inter.mp hx).1))
  have hb₃ : (A ∩ E₃).card ≤ b₃ :=
    h₃ _ inter_subset_right (Set.IsSidon.subset hA.2.1 (by intro x hx; exact (mem_inter.mp hx).1))
  have hc := card_le_card hsub
  have hu₁ := card_union_le S (A ∩ E₁)
  have hu₂ := card_union_le (S ∪ (A ∩ E₁)) (A ∩ E₂)
  have hu₃ := card_union_le (S ∪ (A ∩ E₁) ∪ (A ∩ E₂)) (A ∩ E₃)
  exact ⟨A, hSA, hA, by omega⟩

/-- The manuscript's two short boundary intervals and one residue class cost `12 p` marks. -/
theorem maximal_completion_card_le_fourteen_mul
    {N p u₁ u₂ L₁ L₂ : ℕ} {S : Finset ℕ}
    (hp : 1 ≤ p) (hN : N / p ≤ p ^ 2)
    (hL₁ : L₁ ≤ 10 * p ^ 2) (hL₂ : L₂ ≤ 10 * p ^ 2)
    (hS : S ⊆ Icc 1 N) (hs : IsSidon (S : Set ℕ)) (hcard : S.card ≤ 2 * p)
    (hblocked : ∀ x ∈ Icc 1 N, x ∉ S →
      x ∉ Icc u₁ (u₁ + L₁) → x ∉ Icc u₂ (u₂ + L₂) → ¬ p ∣ x →
      ¬ IsSidon ((S : Set ℕ) ∪ {x})) :
    ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧ A.card ≤ 14 * p := by
  let E₃ := (Icc 1 N).filter fun x => p ∣ x
  have h₁ : ∀ T : Finset ℕ, T ⊆ Icc u₁ (u₁ + L₁) →
      IsSidon (T : Set ℕ) → T.card ≤ 5 * p := by
    intro T hT hsid
    exact sidon_interval_count_five_mul hp hL₁ hsid fun x hx => mem_Icc.mp (hT hx)
  have h₂ : ∀ T : Finset ℕ, T ⊆ Icc u₂ (u₂ + L₂) →
      IsSidon (T : Set ℕ) → T.card ≤ 5 * p := by
    intro T hT hsid
    exact sidon_interval_count_five_mul hp hL₂ hsid fun x hx => mem_Icc.mp (hT hx)
  have h₃ : ∀ T : Finset ℕ, T ⊆ E₃ → IsSidon (T : Set ℕ) → T.card ≤ 2 * p := by
    intro T hT hsid
    apply sidon_multiples_count hp hN hsid
    · intro x hx
      exact (mem_filter.mp (hT hx)).2
    · intro x hx
      exact (mem_Icc.mp (mem_filter.mp (hT hx)).1).2
  have hb : ∀ x ∈ Icc 1 N, x ∉ S → x ∉ Icc u₁ (u₁ + L₁) →
      x ∉ Icc u₂ (u₂ + L₂) → x ∉ E₃ → ¬ IsSidon ((S : Set ℕ) ∪ {x}) := by
    intro x hx hxS hx₁ hx₂ hx₃
    apply hblocked x hx hxS hx₁ hx₂
    intro hdiv
    exact hx₃ (mem_filter.mpr ⟨hx, hdiv⟩)
  obtain ⟨A, _, hA, hbound⟩ :=
    exists_maximal_completion_with_exception_bounds hS hs hb h₁ h₂ h₃
  exact ⟨A, hA, by omega⟩

/-- A maximal set gives an upper bound on the challenge's minimum cardinality. -/
theorem minMaximalSidonSet_le {N : ℕ} {A : Finset ℕ}
    (hA : Set.IsMaximalSidonSetIn (A : Set ℕ) N) :
    Erdos156.minMaximalSidonSet N ≤ A.card := by
  classical
  apply Nat.sInf_le
  change A.card ∈ ((Icc 1 N).powerset.filter fun B : Finset ℕ =>
    Set.IsMaximalSidonSetIn (B : Set ℕ) N).image card
  apply mem_image.mpr
  refine ⟨A, mem_filter.mpr ⟨mem_powerset.mpr ?_, hA⟩, rfl⟩
  intro x hx
  exact mem_Icc.mpr (hA.1 hx)

/-- The minimum in the problem statement is attained by a maximal Sidon set. -/
theorem minMaximalSidonSet_attained (N : ℕ) :
    ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧
      A.card = Erdos156.minMaximalSidonSet N := by
  classical
  obtain ⟨S, _, hS⟩ := exists_maximal_completion (N := N) (S := ∅)
    (empty_subset _) (by simp [IsSidon])
  let candidates := (Icc 1 N).powerset.filter fun A : Finset ℕ =>
    Set.IsMaximalSidonSetIn (A : Set ℕ) N
  have hmem : S ∈ candidates := by
    simp only [candidates, mem_filter, mem_powerset]
    exact ⟨fun x hx => mem_Icc.mpr (hS.1 hx), hS⟩
  have hne : ((candidates.image card : Finset ℕ) : Set ℕ).Nonempty :=
    ⟨S.card, mem_image.mpr ⟨S, hmem, rfl⟩⟩
  obtain ⟨A, hA, heq⟩ := mem_image.mp (Nat.sInf_mem hne)
  exact ⟨A, (mem_filter.mp hA).2, heq⟩

/-- Exact reformulation of the challenge as the manuscript's construction goal. -/
theorem target_iff_small_maximal_sets :
    (fcTypeOfName% "Erdos156.erdos_156") ↔
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ,
        Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧
        (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 3 : ℝ) := by
  rw [true_iff, Asymptotics.isBigO_iff']
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, h.mono fun N hN => ?_⟩
    obtain ⟨A, hA, heq⟩ := minMaximalSidonSet_attained N
    refine ⟨A, hA, ?_⟩
    simpa [heq, Real.norm_eq_abs, abs_of_nonneg, Real.rpow_nonneg] using hN
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, h.mono fun N hN => ?_⟩
    obtain ⟨A, hA, hbound⟩ := hN
    have hmin : (Erdos156.minMaximalSidonSet N : ℝ) ≤ A.card := by
      exact_mod_cast minMaximalSidonSet_le hA
    simpa [Real.norm_eq_abs, abs_of_nonneg, Real.rpow_nonneg] using hmin.trans hbound

end Bounty

namespace Bounty

open Finset Filter

def parameterSigma (d t : ℕ) : ℕ := if t < d then 1 else 0

def parameterEpsilon (p H t : ℕ) : ℕ := if t ^ 2 % p < H then 1 else 0

def parameterPartner (p d t : ℕ) : ℕ := if t < d then t + p - d else t - d

/-- The winding choices are exactly the two comparisons used in the phase count. -/
theorem quadratic_difference_canonical {p d H t : ℕ}
    (hp : 0 < p) (hd : d < p) (hH0 : 0 < H) (hH : H < p) (ht : t < p)
    (heq : 2 * (d : ZMod p) * t = H + (d : ZMod p) ^ 2) :
    parameterPartner p d t < p ∧
      (quadraticMark p t : ℤ) - quadraticMark p (parameterPartner p d t) =
        d - (p : ℤ) * parameterSigma d t + 2 * p * H -
          2 * (p : ℤ) ^ 2 * parameterEpsilon p H t := by
  let u := parameterPartner p d t
  have hu : u < p := by dsimp [u, parameterPartner]; split_ifs <;> omega
  have hs : u + d = t + p * parameterSigma d t := by
    dsimp [u, parameterPartner, parameterSigma]
    split_ifs <;> simp <;> omega
  have hsub : (t : ℤ) - u = d - (p : ℤ) * parameterSigma d t := by
    have hz : (u : ℤ) + d = t + (p : ℤ) * parameterSigma d t := by exact_mod_cast hs
    omega
  have huf : (u : ZMod p) = (t : ZMod p) - d := by
    apply eq_sub_of_add_eq
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) hs
  have hq : (t : ZMod p) ^ 2 - (u : ZMod p) ^ 2 = H := by
    rw [huf]
    linear_combination heq
  have hdiv : (p : ℤ) ∣ ((t ^ 2 % p : ℕ) : ℤ) - (u ^ 2 % p : ℕ) - H := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    simpa using sub_eq_zero.mpr hq
  obtain ⟨z, hz⟩ := hdiv
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have htq0 : (0 : ℤ) ≤ (t ^ 2 % p : ℕ) := Nat.cast_nonneg _
  have huq0 : (0 : ℤ) ≤ (u ^ 2 % p : ℕ) := Nat.cast_nonneg _
  have htq : ((t ^ 2 % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt (t ^ 2) hp
  have huq : ((u ^ 2 % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt (u ^ 2) hp
  have hH0z : (0 : ℤ) < H := by exact_mod_cast hH0
  have hHz : (H : ℤ) < p := by exact_mod_cast hH
  have hzlo : -1 ≤ z := by
    by_contra! h
    have : z ≤ -2 := by omega
    nlinarith
  have hzhi : z ≤ 0 := by
    by_contra! h
    have : 1 ≤ z := h
    nlinarith
  refine ⟨hu, ?_⟩
  change (quadraticMark p t : ℤ) - quadraticMark p u = _
  by_cases hsmall : t ^ 2 % p < H
  · have heps : parameterEpsilon p H t = 1 := by simp [parameterEpsilon, hsmall]
    have hz' : z = -1 := by
      have hsmallz : ((t ^ 2 % p : ℕ) : ℤ) < H := by exact_mod_cast hsmall
      have : z = -1 ∨ z = 0 := by omega
      rcases this with h | h
      · exact h
      · rw [h] at hz
        nlinarith
    rw [heps]
    simp only [quadraticMark, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one]
    rw [hz'] at hz
    nlinarith
  · have heps : parameterEpsilon p H t = 0 := by simp [parameterEpsilon, hsmall]
    have hz' : z = 0 := by
      have hsmallz : (H : ℤ) ≤ (t ^ 2 % p : ℕ) := by exact_mod_cast Nat.le_of_not_lt hsmall
      have : z = -1 ∨ z = 0 := by omega
      rcases this with h | h
      · rw [h] at hz
        nlinarith
      · exact h
    rw [heps]
    simp only [quadraticMark, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero,
      sub_zero]
    rw [hz'] at hz
    nlinarith

noncomputable def residueReal {p : ℕ} (z : ZMod p) : ℝ := (z.val : ℝ) / p

theorem residueReal_nonneg {p : ℕ} (z : ZMod p) : 0 ≤ residueReal z := by
  unfold residueReal
  positivity

theorem residueReal_lt_one {p : ℕ} (hp : 0 < p) (z : ZMod p) : residueReal z < 1 := by
  let : NeZero p := ⟨by omega⟩
  rw [residueReal, div_lt_one (by exact_mod_cast hp)]
  exact_mod_cast ZMod.val_lt z

theorem fract_int_div_eq_residueReal {p : ℕ} (hp : 0 < p) (z : ℤ) :
    Int.fract ((z : ℝ) / p) = residueReal (z : ZMod p) := by
  let : NeZero p := ⟨by omega⟩
  rw [Int.fract_div_intCast_eq_div_intCast_mod, residueReal]
  congr 1
  exact_mod_cast (ZMod.val_intCast z).symm

theorem fract_linear_phase {p : ℕ} (hp : 0 < p) (u r : ZMod p) (k : ℕ) :
    Int.fract (residueReal u - residueReal r * k) = residueReal (u - r * (k : ZMod p)) := by
  let : NeZero p := ⟨by omega⟩
  have h := fract_int_div_eq_residueReal hp ((u.val : ℤ) - r.val * k)
  convert h using 1
  · congr 1
    simp only [residueReal, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring
  · congr 1
    simp

theorem fract_quadratic_phase {p : ℕ} (hp : 0 < p) (u r : ZMod p) (k : ℕ) :
    Int.fract (residueReal (u ^ 2) + residueReal (-2 * u * r) * k +
      residueReal (r ^ 2) * (k : ℝ) ^ 2) = residueReal ((u - r * (k : ZMod p)) ^ 2) := by
  let : NeZero p := ⟨by omega⟩
  let z : ℤ := ((u ^ 2).val : ℤ) + (-2 * u * r).val * k + (r ^ 2).val * (k : ℤ) ^ 2
  have h := fract_int_div_eq_residueReal hp z
  convert h using 1
  · congr 1
    simp only [z, residueReal, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow]
    ring
  · congr 1
    simp only [z, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow,
      ZMod.natCast_zmod_val]
    ring

abbrev PhaseVector := Fin 8 → ℝ

abbrev PhaseBox := {v : PhaseVector // ∀ i, 0 ≤ v i ∧ v i ≤ 1}

noncomputable def firstPhase (k : ℕ) : Module.Dual ℝ PhaseVector :=
  LinearMap.proj 0 - (k : ℝ) • LinearMap.proj 1

noncomputable def secondPhase (k : ℕ) : Module.Dual ℝ PhaseVector :=
  LinearMap.proj 2 + (k : ℝ) • LinearMap.proj 3 + ((k : ℝ) ^ 2) • LinearMap.proj 4

noncomputable def firstThreshold : Module.Dual ℝ PhaseVector := LinearMap.proj 5

noncomputable def secondThreshold (k : ℕ) : Module.Dual ℝ PhaseVector :=
  LinearMap.proj 6 - (k : ℝ) • LinearMap.proj 7

@[simp] theorem firstPhase_apply (k : ℕ) (v : PhaseVector) :
    firstPhase k v = v 0 - (k : ℝ) * v 1 := rfl

@[simp] theorem secondPhase_apply (k : ℕ) (v : PhaseVector) :
    secondPhase k v = v 2 + (k : ℝ) * v 3 + (k : ℝ) ^ 2 * v 4 := rfl

@[simp] theorem firstThreshold_apply (v : PhaseVector) : firstThreshold v = v 5 := rfl

@[simp] theorem secondThreshold_apply (k : ℕ) (v : PhaseVector) :
    secondThreshold k v = v 6 - (k : ℝ) * v 7 := rfl

noncomputable def phaseChoice (k : ℕ) (τ : Fin 2) (v : PhaseVector) : Fin 6 :=
  ⟨2 * (τ.val + if Int.fract (firstPhase k v) < firstThreshold v then 1 else 0) +
      if Int.fract (secondPhase k v) < secondThreshold k v then 1 else 0,
    by split_ifs <;> omega⟩

noncomputable def phaseMatrix {m : ℕ} (k : Fin m → ℕ) (τ : Fin 2)
    (v : PhaseVector) : Fin m → Finset (Fin 6) := fun i => {phaseChoice (k i) τ v}

noncomputable def phaseFamily {m : ℕ} (k : Fin m → ℕ) (τ : Fin 2) :
    Finset (Fin m → Finset (Fin 6)) := by
  classical
  exact univ.filter fun F => ∃ v : PhaseBox, phaseMatrix k τ v = F

theorem phaseFamily_rows_nonempty {m : ℕ} (k : Fin m → ℕ) (τ : Fin 2)
    {F : Fin m → Finset (Fin 6)} (hF : F ∈ phaseFamily k τ) (i : Fin m) :
    (F i).Nonempty := by
  classical
  obtain ⟨v, rfl⟩ := (mem_filter.mp hF).2
  exact singleton_nonempty _

/-- The local quadratic choice matrices have a uniform polynomial phase bound. -/
theorem phaseFamily_card_le {m K : ℕ} (k : Fin m → ℕ) (hk : ∀ i, k i ≤ K) (τ : Fin 2) :
    (phaseFamily k τ).card ≤
      (10 * (2 * (m * 2) * (2 * (1 + K + K ^ 2) + 1) + 1) ^ 9) ^ 2 := by
  classical
  let fs : (Fin m × Bool) → Module.Dual ℝ PhaseVector := fun i =>
    if i.2 then secondPhase (k i.1) else firstPhase (k i.1)
  let gs : (Fin m × Bool) → Module.Dual ℝ PhaseVector := fun i =>
    if i.2 then secondThreshold (k i.1) else firstThreshold
  have hbound : ∀ v : PhaseBox, ∀ i : Fin m × Bool,
      -((1 + K + K ^ 2 : ℕ) : ℝ) ≤ fs i v ∧ fs i v ≤ (1 + K + K ^ 2 : ℕ) := by
    intro v i
    obtain ⟨i, b⟩ := i
    have hk0 : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hkK : (k i : ℝ) ≤ K := by exact_mod_cast hk i
    have hksq : (k i : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by nlinarith
    cases b
    · change -((1 + K + K ^ 2 : ℕ) : ℝ) ≤ v.val 0 - (k i : ℝ) * v.val 1 ∧
        v.val 0 - (k i : ℝ) * v.val 1 ≤ (1 + K + K ^ 2 : ℕ)
      have ht0 := v.property 0
      have ht1 := v.property 1
      have hm0 : 0 ≤ (k i : ℝ) * v.val 1 := mul_nonneg hk0 ht1.1
      have hm1 : (k i : ℝ) * v.val 1 ≤ k i := mul_le_of_le_one_right hk0 ht1.2
      push_cast
      constructor <;> nlinarith [sq_nonneg (K : ℝ)]
    · change -((1 + K + K ^ 2 : ℕ) : ℝ) ≤
        v.val 2 + (k i : ℝ) * v.val 3 + (k i : ℝ) ^ 2 * v.val 4 ∧
        v.val 2 + (k i : ℝ) * v.val 3 + (k i : ℝ) ^ 2 * v.val 4 ≤ (1 + K + K ^ 2 : ℕ)
      have ht2 := v.property 2
      have ht3 := v.property 3
      have ht4 := v.property 4
      have hm0 : 0 ≤ (k i : ℝ) * v.val 3 := mul_nonneg hk0 ht3.1
      have hm1 : (k i : ℝ) * v.val 3 ≤ k i := mul_le_of_le_one_right hk0 ht3.2
      have hq0 : 0 ≤ (k i : ℝ) ^ 2 * v.val 4 := mul_nonneg (sq_nonneg _) ht4.1
      have hq1 : (k i : ℝ) ^ 2 * v.val 4 ≤ (k i : ℝ) ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _) ht4.2
      push_cast
      constructor <;> nlinarith
  have hdet : ∀ x y : PhaseBox,
      (∀ i : Fin m × Bool, (Int.fract (fs i x) < gs i x ↔ Int.fract (fs i y) < gs i y)) →
      phaseMatrix k τ x = phaseMatrix k τ y := by
    intro x y hxy
    funext i
    have hs : (Int.fract (firstPhase (k i) x) < firstThreshold x ↔
        Int.fract (firstPhase (k i) y) < firstThreshold y) := by
      simpa [fs, gs] using hxy (i, false)
    have he : (Int.fract (secondPhase (k i) x) < secondThreshold (k i) x ↔
        Int.fract (secondPhase (k i) y) < secondThreshold (k i) y) := by
      simpa [fs, gs] using hxy (i, true)
    have hc : phaseChoice (k i) τ x = phaseChoice (k i) τ y := by
      apply Fin.ext
      simp only [phaseChoice, hs, he]
    simp only [phaseMatrix, hc]
  have h := SignPatterns.fractional_phase_card_le fs gs (fun _ => 0) (fun _ => 0)
    Subtype.val (fun v : PhaseBox => phaseMatrix k τ v) (phaseFamily k τ)
    (1 + K + K ^ 2) (by simpa only [zero_add] using hbound)
    (by intro F hF; exact (mem_filter.mp hF).2) (by simpa only [zero_add] using hdet)
  simpa only [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, show 8 + 2 = 10 from rfl, show 8 + 1 = 9 from rfl] using h

noncomputable def phaseFamilyAll {m : ℕ} (k : Fin m → ℕ) :
    Finset (Fin m → Finset (Fin 6)) := by
  classical
  exact univ.biUnion (phaseFamily k)

theorem phaseFamilyAll_card_le {m K : ℕ} (k : Fin m → ℕ) (hk : ∀ i, k i ≤ K) :
    (phaseFamilyAll k).card ≤
      2 * (10 * (2 * (m * 2) * (2 * (1 + K + K ^ 2) + 1) + 1) ^ 9) ^ 2 := by
  classical
  exact (card_biUnion_le_card_mul univ (phaseFamily k) _
    (fun τ _ => phaseFamily_card_le k hk τ)).trans_eq (by simp)

def rulerIndex (m : ℕ) (i : Fin m) : ℕ := 4 * (i.val + 2 * m * i.val ^ 2)

theorem rulerIndex_le {m : ℕ} (hm : 1 ≤ m) (i : Fin m) : rulerIndex m i ≤ 12 * m ^ 3 := by
  have hi : i.val ≤ m := Nat.le_of_lt i.isLt
  have hm3 : m ≤ m ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hm (show 1 ≤ 3 by decide)
  calc
    rulerIndex m i ≤ 4 * (m ^ 3 + 2 * m * m ^ 2) := by
      unfold rulerIndex
      gcongr
      · exact hi.trans hm3
    _ = 12 * m ^ 3 := by ring

theorem phaseFamilyAll_card_polynomial {m : ℕ} (hm : 1 ≤ m) :
    (phaseFamilyAll (rulerIndex m)).card ≤ (200 * 2048 ^ 18) * m ^ 126 := by
  let B := 1 + 12 * m ^ 3 + (12 * m ^ 3) ^ 2
  let q := 2 * (m * 2) * (2 * B + 1) + 1
  have hm6 : 1 ≤ m ^ 6 := by simpa using Nat.pow_le_pow_left hm 6
  have hm7 : 1 ≤ m ^ 7 := by simpa using Nat.pow_le_pow_left hm 7
  have hm36 : m ^ 3 ≤ m ^ 6 := Nat.pow_le_pow_right hm (by decide)
  have hB : B ≤ 169 * m ^ 6 := by dsimp [B]; nlinarith
  have hB' : 2 * B + 1 ≤ 339 * m ^ 6 := by omega
  have hq : q ≤ 2048 * m ^ 7 := by
    calc
      q = 4 * m * (2 * B + 1) + 1 := by dsimp [q]; ring
      _ ≤ 4 * m * (339 * m ^ 6) + m ^ 7 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hB') hm7
      _ = 1357 * m ^ 7 := by ring
      _ ≤ 2048 * m ^ 7 := Nat.mul_le_mul_right _ (by decide)
  have hc : (phaseFamilyAll (rulerIndex m)).card ≤ 2 * (10 * q ^ 9) ^ 2 :=
    phaseFamilyAll_card_le _ (rulerIndex_le hm)
  have hid (n : ℕ) : 2 * (10 * n ^ 9) ^ 2 = 200 * n ^ 18 := by ring
  calc
    (phaseFamilyAll (rulerIndex m)).card ≤ 200 * q ^ 18 := by simpa only [hid] using hc
    _ ≤ 200 * (2048 * m ^ 7) ^ 18 := by gcongr
    _ = (200 * 2048 ^ 18) * m ^ 126 := by
      rw [mul_pow, ← pow_mul]
      ac_rfl

noncomputable def rulerFamily (m : ℕ) : Finset (Fin m → Finset (Fin 6)) :=
  if m = 0 then ∅ else phaseFamilyAll (rulerIndex m)

theorem exists_sparse_phase_word :
    ∃ m ≥ 1, ∃ w : Fin m → Fin 6, ∀ v : PhaseBox, ∀ τ : Fin 2,
      ∃ i, w i = phaseChoice (rulerIndex m i) τ v := by
  classical
  have hne : ∀ m, ∀ G ∈ rulerFamily m, ∀ i, (G i).Nonempty := by
    intro m G hG i
    by_cases hm : m = 0
    · simp [rulerFamily, hm] at hG
    · simp only [rulerFamily, hm, ite_false, phaseFamilyAll, mem_biUnion, mem_univ,
        true_and] at hG
      obtain ⟨τ, hτ⟩ := hG
      exact phaseFamily_rows_nonempty _ τ hτ i
  have hc : ∀ m, (rulerFamily m).card ≤ (200 * 2048 ^ 18) * m ^ 126 := by
    intro m
    by_cases hm : m = 0
    · simp [rulerFamily, hm]
    · simpa only [rulerFamily, hm, ite_false] using phaseFamilyAll_card_polynomial (by omega : 1 ≤ m)
  obtain ⟨m, hm, w, hw⟩ := exists_hitting_word_of_polynomial_bound (by decide : 1 < 6)
    rulerFamily hne hc 1
  refine ⟨m, hm, w, ?_⟩
  intro v τ
  have hmem : phaseMatrix (rulerIndex m) τ v ∈ rulerFamily m := by
    simp only [rulerFamily, show m ≠ 0 by omega, ite_false, phaseFamilyAll, mem_biUnion,
      mem_univ, true_and]
    refine ⟨τ, mem_filter.mpr ⟨mem_univ _, v, rfl⟩⟩
  obtain ⟨i, hi⟩ := hw _ hmem
  exact ⟨i, mem_singleton.mp hi⟩

noncomputable def modularVector {p : ℕ} (u r : ZMod p) (d Y : ℕ) : PhaseVector :=
  ![residueReal u, residueReal r, residueReal (u ^ 2), residueReal (-2 * u * r),
    residueReal (r ^ 2), (d : ℝ) / p, (Y : ℝ) / p, 1 / (p : ℝ)]

theorem modularVector_inBox {p : ℕ} (hp : 0 < p) (u r : ZMod p)
    {d Y : ℕ} (hd : d ≤ p) (hY : Y ≤ p) :
    ∀ i, 0 ≤ modularVector u r d Y i ∧ modularVector u r d Y i ≤ 1 := by
  have hnat (a : ℕ) (ha : a ≤ p) : 0 ≤ (a : ℝ) / p ∧ (a : ℝ) / p ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
      exact_mod_cast ha
  have hres (z : ZMod p) : 0 ≤ residueReal z ∧ residueReal z ≤ 1 :=
    ⟨residueReal_nonneg z, (residueReal_lt_one hp z).le⟩
  intro i
  fin_cases i
  · simpa [modularVector] using hres u
  · simpa [modularVector] using hres r
  · simpa [modularVector] using hres (u ^ 2)
  · simpa [modularVector] using hres (-2 * u * r)
  · simpa [modularVector] using hres (r ^ 2)
  · simpa [modularVector] using hnat d hd
  · simpa [modularVector] using hnat Y hY
  · simpa [modularVector] using hnat 1 (by omega)

theorem residueReal_lt_div {p a : ℕ} (hp : 0 < p) (z : ZMod p) :
    residueReal z < (a : ℝ) / p ↔ z.val < a := by
  rw [residueReal, div_lt_div_iff_of_pos_right (by exact_mod_cast hp : (0 : ℝ) < p)]
  exact Nat.cast_lt

theorem phaseChoice_modular {p : ℕ} (hp : 0 < p) (u r : ZMod p)
    (d Y k : ℕ) (hk : k ≤ Y) (τ : Fin 2) :
    (phaseChoice k τ (modularVector u r d Y)).val =
      2 * (τ.val + parameterSigma d (u - r * (k : ZMod p)).val) +
        parameterEpsilon p (Y - k) (u - r * (k : ZMod p)).val := by
  let : NeZero p := ⟨by omega⟩
  let t : ZMod p := u - r * (k : ZMod p)
  change (phaseChoice k τ (modularVector u r d Y)).val =
    2 * (τ.val + parameterSigma d t.val) + parameterEpsilon p (Y - k) t.val
  have hfirst : Int.fract (firstPhase k (modularVector u r d Y)) = residueReal t := by
    simpa [modularVector, t, mul_comm] using fract_linear_phase hp u r k
  have hsecond : Int.fract (secondPhase k (modularVector u r d Y)) = residueReal (t ^ 2) := by
    simpa [modularVector, t, mul_comm] using fract_quadratic_phase hp u r k
  have hthreshold : secondThreshold k (modularVector u r d Y) = ((Y - k : ℕ) : ℝ) / p := by
    change (Y : ℝ) / p - (k : ℝ) * (1 / (p : ℝ)) = ((Y - k : ℕ) : ℝ) / p
    rw [Nat.cast_sub hk]
    ring
  have hval : (t ^ 2).val = t.val ^ 2 % p := by
    calc
      (t ^ 2).val = (((t.val ^ 2 : ℕ) : ZMod p)).val := by congr 1; simp
      _ = _ := ZMod.val_natCast _ _
  have hs : (Int.fract (firstPhase k (modularVector u r d Y)) <
      firstThreshold (modularVector u r d Y)) ↔ t.val < d := by
    rw [hfirst]
    simpa [modularVector] using residueReal_lt_div hp (a := d) t
  have he : (Int.fract (secondPhase k (modularVector u r d Y)) <
      secondThreshold k (modularVector u r d Y)) ↔ t.val ^ 2 % p < Y - k := by
    rw [hsecond, hthreshold]
    exact (residueReal_lt_div hp (a := Y - k) (t ^ 2)).trans (by rw [hval])
  simp only [phaseChoice, hs, he, parameterSigma, parameterEpsilon]

/-- The normalized phase labels produce actual differences of the integer seed. -/
theorem phaseChoice_covers {p d Y k : ℕ} (hp : 0 < p) (hd : d < p)
    (hY : Y < p) (hk : k < Y) (τ : Fin 2) (r : ZMod p)
    (hr : 2 * (d : ZMod p) * r = 1) (w : Fin 6)
    (hw : w = phaseChoice k τ (modularVector (r * ((Y : ZMod p) + (d : ZMod p) ^ 2)) r d Y)) :
    ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (d : ℤ) + p * τ.val + 2 * p * Y =
        a - b + (p : ℤ) * ((2 * k + w.val / 2 : ℕ) : ℤ) +
          ((w.val % 2 : ℕ) : ℤ) * (2 * (p : ℤ) ^ 2) := by
  let : NeZero p := ⟨by omega⟩
  let u : ZMod p := r * ((Y : ZMod p) + (d : ZMod p) ^ 2)
  let t : ZMod p := u - r * (k : ZMod p)
  have ht : t.val < p := ZMod.val_lt _
  have hH0 : 0 < Y - k := by omega
  have hHp : Y - k < p := by omega
  have hfield : 2 * (d : ZMod p) * t.val = ((Y - k : ℕ) : ZMod p) + (d : ZMod p) ^ 2 := by
    rw [ZMod.natCast_zmod_val, Nat.cast_sub (Nat.le_of_lt hk)]
    change 2 * (d : ZMod p) * (r * ((Y : ZMod p) + (d : ZMod p) ^ 2) - r * (k : ZMod p)) = _
    calc
      _ = (2 * (d : ZMod p) * r) * ((Y : ZMod p) - (k : ZMod p) + (d : ZMod p) ^ 2) := by ring
      _ = _ := by rw [hr]; ring
  have hcanon := quadratic_difference_canonical hp hd hH0 hHp ht hfield
  have hwval : w.val = 2 * (τ.val + parameterSigma d t.val) + parameterEpsilon p (Y - k) t.val := by
    rw [hw]
    exact phaseChoice_modular hp u r d Y k (Nat.le_of_lt hk) τ
  have hσ : parameterSigma d t.val ≤ 1 := by unfold parameterSigma; split_ifs <;> omega
  have hε : parameterEpsilon p (Y - k) t.val ≤ 1 := by
    unfold parameterEpsilon
    split_ifs <;> omega
  have hwdiv : w.val / 2 = τ.val + parameterSigma d t.val := by omega
  have hwmod : w.val % 2 = parameterEpsilon p (Y - k) t.val := by omega
  refine ⟨quadraticMark p t.val, mem_image.mpr ⟨t.val, mem_range.mpr ht, rfl⟩,
    quadraticMark p (parameterPartner p d t.val),
    mem_image.mpr ⟨_, mem_range.mpr hcanon.1, rfl⟩, ?_⟩
  rw [hwdiv, hwmod]
  have hid := hcanon.2
  rw [Nat.cast_sub (Nat.le_of_lt hk)] at hid
  push_cast
  nlinarith [hid]

theorem natural_pair_of_sum_sq {i j k l : ℕ} (hs : i + j = k + l)
    (hq : i ^ 2 + j ^ 2 = k ^ 2 + l ^ 2) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hs' : (i : ℤ) + j = k + l := by exact_mod_cast hs
  have hq' : (i : ℤ) ^ 2 + (j : ℤ) ^ 2 = (k : ℤ) ^ 2 + (l : ℤ) ^ 2 := by exact_mod_cast hq
  have hp : (i : ℤ) * j = (k : ℤ) * l := by nlinarith
  have hf : ((i : ℤ) - k) * ((i : ℤ) - l) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · left
    have := sub_eq_zero.mp h
    constructor <;> omega
  · right
    have := sub_eq_zero.mp h
    constructor <;> omega

def rulerValue (m i : ℕ) : ℕ := i + 2 * m * i ^ 2

theorem rulerValue_pair {m i j k l : ℕ} (hm : 0 < m)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (h : rulerValue m i + rulerValue m j = rulerValue m k + rulerValue m l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hmpos : 0 < 2 * m := Nat.mul_pos (by decide) hm
  have hform : i + j + 2 * m * (i ^ 2 + j ^ 2) = k + l + 2 * m * (k ^ 2 + l ^ 2) := by
    unfold rulerValue at h
    nlinarith
  have hs : i + j = k + l := by
    have he := congrArg (fun n => n % (2 * m)) hform
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : i + j < 2 * m),
      Nat.mod_eq_of_lt (by omega : k + l < 2 * m)] using he
  have hq : i ^ 2 + j ^ 2 = k ^ 2 + l ^ 2 := by nlinarith
  exact natural_pair_of_sum_sq hs hq

def alphabetDelta {m : ℕ} (w : Fin m → Fin 6) (i : Fin m) : ℕ :=
  2 * rulerIndex m i + (w i).val / 2

def alphabetEpsilon {m : ℕ} (w : Fin m → Fin 6) (i : Fin m) : ℕ := (w i).val % 2

def alphabetMax (m : ℕ) : ℕ := 24 * m ^ 3 + 2

theorem alphabetDelta_le {m : ℕ} (hm : 1 ≤ m) (w : Fin m → Fin 6) (i : Fin m) :
    alphabetDelta w i ≤ alphabetMax m := by
  have hk := rulerIndex_le hm i
  have hw := (w i).isLt
  unfold alphabetDelta alphabetMax
  omega

theorem alphabetEpsilon_le {m : ℕ} (w : Fin m → Fin 6) (i : Fin m) :
    alphabetEpsilon w i ≤ 1 := by unfold alphabetEpsilon; omega

theorem alphabetDelta_pair {m : ℕ} (hm : 1 ≤ m) (w : Fin m → Fin 6)
    (i j k l : Fin m) (h : alphabetDelta w i + alphabetDelta w j =
      alphabetDelta w k + alphabetDelta w l) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hform : 8 * (rulerValue m i.val + rulerValue m j.val) + ((w i).val / 2 + (w j).val / 2) =
      8 * (rulerValue m k.val + rulerValue m l.val) + ((w k).val / 2 + (w l).val / 2) := by
    calc
      _ = alphabetDelta w i + alphabetDelta w j := by
        unfold alphabetDelta rulerIndex rulerValue
        ring
      _ = alphabetDelta w k + alphabetDelta w l := h
      _ = _ := by unfold alphabetDelta rulerIndex rulerValue; ring
  have hsmall₁ : (w i).val / 2 + (w j).val / 2 < 8 := by
    have := (w i).isLt
    have := (w j).isLt
    omega
  have hsmall₂ : (w k).val / 2 + (w l).val / 2 < 8 := by
    have := (w k).isLt
    have := (w l).isLt
    omega
  have he := congrArg (fun n => n % 8) hform
  simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsmall₁,
    Nat.mod_eq_of_lt hsmall₂] at he
  have hbase : rulerValue m i.val + rulerValue m j.val = rulerValue m k.val + rulerValue m l.val := by
    omega
  rcases rulerValue_pair (by omega) i.isLt j.isLt k.isLt l.isLt hbase with h | h
  · exact Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩
  · exact Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩

theorem alphabetDelta_isSidon {m : ℕ} (hm : 1 ≤ m) (w : Fin m → Fin 6) :
    IsSidon ((univ.image (alphabetDelta w) : Finset ℕ) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd heq
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := mem_image.mp hc
  obtain ⟨l, _, rfl⟩ := mem_image.mp hd
  rcases alphabetDelta_pair hm w i k j l heq with h | h
  · exact Or.inl ⟨congrArg (alphabetDelta w) h.1, congrArg (alphabetDelta w) h.2⟩
  · exact Or.inr ⟨congrArg (alphabetDelta w) h.1, congrArg (alphabetDelta w) h.2⟩

theorem exists_inverse_twice {p d : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) : ∃ r : ZMod p, 2 * (d : ZMod p) * r = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro heq
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp heq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact hp.ne_one h
    · exact hodd h
  have hd : (d : ZMod p) ≠ 0 := by
    intro heq
    have hm := (ZMod.natCast_eq_natCast_iff' d 0 p).mp (by simpa using heq)
    simp only [Nat.mod_eq_of_lt hdp, Nat.zero_mod] at hm
    omega
  exact ⟨(2 * (d : ZMod p))⁻¹, mul_inv_cancel₀ (mul_ne_zero htwo hd)⟩

theorem phase_word_covers_decomposed {m p d Y : ℕ} (k : Fin m → ℕ) (w : Fin m → Fin 6)
    (hw : ∀ v : PhaseBox, ∀ τ : Fin 2, ∃ i, w i = phaseChoice (k i) τ v)
    (hp : p.Prime) (hodd : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (hY : Y < p) (hk : ∀ i, k i < Y) (τ : Fin 2) :
    ∃ i, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (d : ℤ) + p * τ.val + 2 * p * Y =
        a - b + (p : ℤ) * ((2 * k i + (w i).val / 2 : ℕ) : ℤ) +
          (((w i).val % 2 : ℕ) : ℤ) * (2 * (p : ℤ) ^ 2) := by
  obtain ⟨r, hr⟩ := exists_inverse_twice hp hodd hd0 hdp
  let u : ZMod p := r * ((Y : ZMod p) + (d : ZMod p) ^ 2)
  let v : PhaseBox := ⟨modularVector u r d Y, modularVector_inBox hp.pos u r hdp.le hY.le⟩
  obtain ⟨i, hi⟩ := hw v τ
  refine ⟨i, ?_⟩
  exact phaseChoice_covers hp.pos hdp hY (hk i) τ r hr (w i) hi

theorem sparse_word_covers {m : ℕ} (hm : 1 ≤ m) (w : Fin m → Fin 6)
    (hw : ∀ v : PhaseBox, ∀ τ : Fin 2, ∃ i, w i = phaseChoice (rulerIndex m i) τ v)
    {p y : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hlower : 2 * p * (alphabetMax m + 2) ≤ y)
    (hupper : y < 2 * p * (p - 1)) (hdiv : ¬ p ∣ y) :
    ∃ i, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (y : ℤ) = a - b + (p : ℤ) * alphabetDelta w i + alphabetEpsilon w i * (2 * (p : ℤ) ^ 2) := by
  let d := y % p
  let q := y / p
  let Y := q / 2
  let τ : Fin 2 := ⟨q % 2, Nat.mod_lt _ (by decide)⟩
  have hpd : 0 < 2 * p := Nat.mul_pos (by decide) hp.pos
  have hYeq : Y = y / (2 * p) := by
    dsimp [Y, q]
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p 2]
  have hYlow : alphabetMax m + 2 ≤ Y := by
    rw [hYeq]
    apply (Nat.le_div_iff_mul_le hpd).mpr
    nlinarith [hlower]
  have hY : Y < p := by
    rw [hYeq]
    have h : y / (2 * p) < p - 1 := (Nat.div_lt_iff_lt_mul hpd).mpr (by nlinarith [hupper])
    omega
  have hdp : d < p := Nat.mod_lt _ hp.pos
  have hd0 : 0 < d := by
    have hdne : d ≠ 0 := by
      intro hd
      exact hdiv (Nat.dvd_of_mod_eq_zero hd)
    omega
  have hk : ∀ i : Fin m, rulerIndex m i < Y := by
    intro i
    have hi := rulerIndex_le hm i
    unfold alphabetMax at hYlow
    omega
  have hy : y = d + p * τ.val + 2 * p * Y := by
    have hq : q = q % 2 + 2 * (q / 2) := (Nat.mod_add_div q 2).symm
    calc
      y = d + p * q := (Nat.mod_add_div y p).symm
      _ = d + p * (q % 2 + 2 * (q / 2)) := congrArg (fun n => d + p * n) hq
      _ = _ := by dsimp [τ, Y]; ring
  obtain ⟨i, a, ha, b, hb, hab⟩ :=
    phase_word_covers_decomposed (rulerIndex m) w hw hp hodd hd0 hdp hY hk τ
  refine ⟨i, a, ha, b, hb, ?_⟩
  have hyz : (y : ℤ) = (d : ℤ) + (p : ℤ) * τ.val + 2 * p * Y := by exact_mod_cast hy
  simpa only [alphabetDelta, alphabetEpsilon] using hyz.trans hab

/-- A fixed finite Sidon alphabet covers every required interior nonmultiple of every odd prime. -/
theorem exists_fixed_translate_alphabet :
    ∃ m ≥ 1, ∃ w : Fin m → Fin 6,
      IsSidon ((univ.image (alphabetDelta w) : Finset ℕ) : Set ℕ) ∧
      (∀ i, alphabetDelta w i ≤ alphabetMax m ∧ alphabetEpsilon w i ≤ 1) ∧
      ∀ (p y : ℕ), p.Prime → p ≠ 2 →
        2 * p * (alphabetMax m + 2) ≤ y → y < 2 * p * (p - 1) → ¬ p ∣ y →
        ∃ i, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
          (y : ℤ) = a - b + (p : ℤ) * alphabetDelta w i + alphabetEpsilon w i * (2 * (p : ℤ) ^ 2) := by
  obtain ⟨m, hm, w, hw⟩ := exists_sparse_phase_word
  refine ⟨m, hm, w, alphabetDelta_isSidon hm w,
    fun i => ⟨alphabetDelta_le hm w i, alphabetEpsilon_le w i⟩, ?_⟩
  intro p y hp hodd hlo hhi hdiv
  exact sparse_word_covers hm w hw hp hodd hlo hhi hdiv

end Bounty

namespace Bounty.Window

open Finset Filter

abbrev FloorVector := Fin 3 → ℝ
abbrev FloorBox := {v : FloorVector //
  (0 ≤ v 0 ∧ v 0 ≤ 1) ∧ (0 ≤ v 1 ∧ v 1 ≤ 2) ∧ (0 ≤ v 2 ∧ v 2 ≤ 1)}

def floorCap (R : ℕ) : ℕ := (R + 1) ^ 2

noncomputable def rulerPhase (j : ℕ) : Module.Dual ℝ FloorVector :=
  LinearMap.proj 0 + (j : ℝ) • LinearMap.proj 1 + ((j : ℝ) ^ 2) • LinearMap.proj 2

@[simp] theorem rulerPhase_apply (j : ℕ) (v : FloorVector) :
    rulerPhase j v = v 0 + (j : ℝ) * v 1 + (j : ℝ) ^ 2 * v 2 := rfl

theorem rulerPhase_bounds {R : ℕ} (v : FloorBox) (j : Fin R) :
    0 ≤ rulerPhase j.val v ∧ rulerPhase j.val v ≤ floorCap R := by
  have h0 := v.property.1
  have h1 := v.property.2.1
  have h2 := v.property.2.2
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hjR : (j.val : ℝ) ≤ R := by exact_mod_cast j.isLt.le
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hjsq : (j.val : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by nlinarith
  have hx0 : 0 ≤ (j.val : ℝ) * v.val 1 := mul_nonneg hj0 h1.1
  have hx1 : (j.val : ℝ) * v.val 1 ≤ (j.val : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left h1.2 hj0
  have hy0 : 0 ≤ (j.val : ℝ) ^ 2 * v.val 2 := mul_nonneg (sq_nonneg _) h2.1
  have hy1 : (j.val : ℝ) ^ 2 * v.val 2 ≤ (j.val : ℝ) ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg _) h2.2
  simp only [rulerPhase_apply, floorCap, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

noncomputable def floorLabel (R : ℕ) (v : FloorBox) (j : Fin R) : Fin (floorCap R + 1) :=
  ⟨⌊rulerPhase j.val v⌋₊,
    Nat.lt_succ_of_le (Nat.floor_le_of_le (rulerPhase_bounds v j).2)⟩

noncomputable def floorFamily (R : ℕ) : Finset (Fin R → Fin (floorCap R + 1)) := by
  classical
  exact univ.filter fun E => ∃ v : FloorBox, floorLabel R v = E

/-- The integer carry vectors of a quadratic ruler have polynomially many possibilities. -/
theorem floorFamily_card_le (R : ℕ) :
    (floorFamily R).card ≤ (5 * (R * (2 * floorCap R + 1) + 1) ^ 4) ^ 2 := by
  classical
  let J := Fin R × ↥(Icc (-(floorCap R : ℤ)) (floorCap R))
  let f : J → Module.Dual ℝ FloorVector := fun i => rulerPhase i.1.val
  let c : J → ℝ := fun i => -(i.2 : ℤ)
  have hdet : ∀ x y : FloorBox, (∀ i : J,
      (0 < c i + f i x ↔ 0 < c i + f i y) ∧
      (c i + f i x < 0 ↔ c i + f i y < 0)) → floorLabel R x = floorLabel R y := by
    intro x y hxy
    funext j
    apply Fin.ext
    have hx := rulerPhase_bounds x j
    have hy := rulerPhase_bounds y j
    have hfloor : ⌊rulerPhase j.val x⌋ = ⌊rulerPhase j.val y⌋ := by
      apply SignPatterns.floor_eq_of_integer_cuts
        (show -(floorCap R : ℝ) ≤ rulerPhase j.val x ∧ rulerPhase j.val x ≤ floorCap R by
          constructor <;> nlinarith)
        (show -(floorCap R : ℝ) ≤ rulerPhase j.val y ∧ rulerPhase j.val y ≤ floorCap R by
          constructor <;> nlinarith)
      intro k hk
      have h := (hxy (j, ⟨k, hk⟩)).2
      simpa only [c, f, neg_add_eq_sub] using h
    change ⌊rulerPhase j.val x⌋₊ = ⌊rulerPhase j.val y⌋₊
    rw [← Int.floor_toNat, ← Int.floor_toNat, hfloor]
  have hc := SignPatterns.affine_sign_determined_card_le f c Subtype.val (floorLabel R)
    (floorFamily R) (by intro E hE; exact (mem_filter.mp hE).2) hdet
  have hcuts : Fintype.card ↥(Icc (-(floorCap R : ℤ)) (floorCap R)) = 2 * floorCap R + 1 := by
    rw [Fintype.card_coe, Int.card_Icc]
    omega
  simpa only [J, Fintype.card_prod, Fintype.card_fin, hcuts, Module.finrank_fin_fun,
    show 3 + 2 = 5 from rfl, show 3 + 1 = 4 from rfl] using hc

theorem floorFamily_card_polynomial {R : ℕ} (hR : 1 ≤ R) :
    (floorFamily R).card ≤ (25 * 10 ^ 8) * R ^ 24 := by
  have hR2 : 1 ≤ R ^ 2 := by simpa using Nat.pow_le_pow_left hR 2
  have hR3 : 1 ≤ R ^ 3 := by simpa using Nat.pow_le_pow_left hR 3
  have hcap : floorCap R ≤ 4 * R ^ 2 := by unfold floorCap; nlinarith
  have htwice : 2 * floorCap R + 1 ≤ 9 * R ^ 2 := by omega
  have hbase : R * (2 * floorCap R + 1) + 1 ≤ 10 * R ^ 3 := by
    calc
      R * (2 * floorCap R + 1) + 1 ≤ R * (9 * R ^ 2) + R ^ 3 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ htwice) hR3
      _ = _ := by ring
  have hid (x : ℕ) : (5 * x ^ 4) ^ 2 = 25 * x ^ 8 := by ring
  calc
    (floorFamily R).card ≤ 25 * (R * (2 * floorCap R + 1) + 1) ^ 8 := by
      simpa only [hid] using floorFamily_card_le R
    _ ≤ 25 * (10 * R ^ 3) ^ 8 := by gcongr
    _ = (25 * 10 ^ 8) * R ^ 24 := by rw [mul_pow, ← pow_mul]; ac_rfl

abbrev Feature := Fin 5 → ℤ
abbrev CoeffVector := (Fin 5 → ℝ) × ((Fin 5 × Fin 5 → ℝ) × ((Fin 5 → ℝ) × ℝ))
abbrev CoeffBox := {v : CoeffVector //
  (∀ i, 0 ≤ v.1 i ∧ v.1 i ≤ 1) ∧ (∀ i, 0 ≤ v.2.1 i ∧ v.2.1 i ≤ 1)}

noncomputable def linearPhase (F : Feature) : Module.Dual ℝ CoeffVector where
  toFun v := ∑ i, (F i : ℝ) * v.1 i
  map_add' v w := by simp [mul_add, sum_add_distrib]
  map_smul' r v := by simp [smul_eq_mul, Finset.mul_sum, mul_left_comm]

noncomputable def squarePhase (F : Feature) : Module.Dual ℝ CoeffVector where
  toFun v := ∑ ij : Fin 5 × Fin 5, (F ij.1 : ℝ) * (F ij.2 : ℝ) * v.2.1 ij
  map_add' v w := by simp [mul_add, sum_add_distrib]
  map_smul' r v := by simp [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

noncomputable def heightPhase (F : Feature) : Module.Dual ℝ CoeffVector where
  toFun v := ∑ i, (F i : ℝ) * v.2.2.1 i
  map_add' v w := by simp [mul_add, sum_add_distrib]
  map_smul' r v := by simp [smul_eq_mul, Finset.mul_sum, mul_left_comm]

def residueThreshold : Module.Dual ℝ CoeffVector where
  toFun v := v.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem linearPhase_apply (F : Feature) (v : CoeffVector) :
    linearPhase F v = ∑ i, (F i : ℝ) * v.1 i := rfl

@[simp] theorem squarePhase_apply (F : Feature) (v : CoeffVector) :
    squarePhase F v = ∑ ij : Fin 5 × Fin 5, (F ij.1 : ℝ) * (F ij.2 : ℝ) * v.2.1 ij := rfl

@[simp] theorem heightPhase_apply (F : Feature) (v : CoeffVector) :
    heightPhase F v = ∑ i, (F i : ℝ) * v.2.2.1 i := rfl

@[simp] theorem residueThreshold_apply (v : CoeffVector) : residueThreshold v = v.2.2.2 := rfl

theorem sum_product_abs_bound {ι : Type*} [Fintype ι] (a x : ι → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (ha : ∀ i, |a i| ≤ L) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    |∑ i, a i * x i| ≤ Fintype.card ι * L := by
  classical
  calc
    |∑ i, a i * x i| ≤ ∑ i, |a i * x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, L := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hx i).1]
      calc
        |a i| * x i ≤ L * x i := mul_le_mul_of_nonneg_right (ha i) (hx i).1
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left (hx i).2 hL
        _ = L := mul_one _
    _ = Fintype.card ι * L := by simp

theorem linearPhase_abs_le (F : Feature) {L : ℕ} (hF : ∀ i, |F i| ≤ L) (v : CoeffBox) :
    |linearPhase F v| ≤ 5 * (L : ℝ) := by
  simpa only [linearPhase_apply, Fintype.card_fin, Nat.cast_ofNat] using
    sum_product_abs_bound (fun i => (F i : ℝ)) v.val.1 (Nat.cast_nonneg L)
      (fun i => by exact_mod_cast hF i) v.property.1

theorem squarePhase_abs_le (F : Feature) {L : ℕ} (hF : ∀ i, |F i| ≤ L) (v : CoeffBox) :
    |squarePhase F v| ≤ 25 * (L : ℝ) ^ 2 := by
  have hprod : ∀ ij : Fin 5 × Fin 5, |(F ij.1 : ℝ) * (F ij.2 : ℝ)| ≤ (L : ℝ) ^ 2 := by
    intro ij
    rw [abs_mul, pow_two]
    apply mul_le_mul
    · exact_mod_cast hF ij.1
    · exact_mod_cast hF ij.2
    · exact abs_nonneg _
    · exact Nat.cast_nonneg _
  simpa only [squarePhase_apply, Fintype.card_prod, Fintype.card_fin,
    Nat.reduceMul, Nat.cast_ofNat] using
      sum_product_abs_bound (fun ij => (F ij.1 : ℝ) * (F ij.2 : ℝ)) v.val.2.1
        (sq_nonneg (L : ℝ)) hprod v.property.2

noncomputable def windowMatrix {R b : ℕ} (features : Fin R → Fin b → Feature)
    (sigma : Fin R → Fin b → Bool) (epsilon : Fin b → Bool) (v : CoeffVector) :
    Fin R → Finset (Fin b) := by
  classical
  exact fun j => univ.filter fun l =>
    ((Int.fract (linearPhase (features j l) v) < residueThreshold v) ↔ sigma j l = true) ∧
    ((Int.fract (squarePhase (features j l) v) < heightPhase (features j l) v) ↔ epsilon l = true)

noncomputable def windowFamily {R b : ℕ} (features : Fin R → Fin b → Feature)
    (sigma : Fin R → Fin b → Bool) (epsilon : Fin b → Bool) :
    Finset (Fin R → Finset (Fin b)) := by
  classical
  exact univ.filter fun G => ∃ v : CoeffBox, windowMatrix features sigma epsilon v = G

/-- Fixed-dimensional feature phases give a uniform bound for all good-label matrices. -/
theorem windowFamily_card_le {R b L : ℕ} (features : Fin R → Fin b → Feature)
    (hfeatures : ∀ j l i, |features j l i| ≤ L)
    (sigma : Fin R → Fin b → Bool) (epsilon : Fin b → Bool) :
    (windowFamily features sigma epsilon).card ≤
      (38 * (2 * (R * b * 2) * (2 * (25 * L ^ 2 + 5 * L) + 1) + 1) ^ 37) ^ 2 := by
  classical
  let fs : ((Fin R × Fin b) × Bool) → Module.Dual ℝ CoeffVector := fun i =>
    if i.2 then squarePhase (features i.1.1 i.1.2) else linearPhase (features i.1.1 i.1.2)
  let gs : ((Fin R × Fin b) × Bool) → Module.Dual ℝ CoeffVector := fun i =>
    if i.2 then heightPhase (features i.1.1 i.1.2) else residueThreshold
  have hbound : ∀ v : CoeffBox, ∀ i : (Fin R × Fin b) × Bool,
      -((25 * L ^ 2 + 5 * L : ℕ) : ℝ) ≤ fs i v ∧ fs i v ≤ (25 * L ^ 2 + 5 * L : ℕ) := by
    intro v i
    obtain ⟨⟨j, l⟩, c⟩ := i
    cases c
    · have h := abs_le.mp (linearPhase_abs_le _ (hfeatures j l) v)
      change -((25 * L ^ 2 + 5 * L : ℕ) : ℝ) ≤ linearPhase (features j l) v ∧
        linearPhase (features j l) v ≤ ((25 * L ^ 2 + 5 * L : ℕ) : ℝ)
      push_cast
      constructor <;> nlinarith [sq_nonneg (L : ℝ)]
    · have h := abs_le.mp (squarePhase_abs_le _ (hfeatures j l) v)
      change -((25 * L ^ 2 + 5 * L : ℕ) : ℝ) ≤ squarePhase (features j l) v ∧
        squarePhase (features j l) v ≤ ((25 * L ^ 2 + 5 * L : ℕ) : ℝ)
      push_cast
      constructor <;> nlinarith
  have hdet : ∀ x y : CoeffBox,
      (∀ i : (Fin R × Fin b) × Bool, (Int.fract (fs i x) < gs i x ↔ Int.fract (fs i y) < gs i y)) →
      windowMatrix features sigma epsilon x = windowMatrix features sigma epsilon y := by
    intro x y hxy
    funext j
    ext l
    have hl := hxy ((j, l), false)
    have hs := hxy ((j, l), true)
    simp only [fs, gs, Bool.false_eq_true, ite_false, ite_true] at hl hs
    simp only [windowMatrix, mem_filter, mem_univ, true_and, hl, hs]
  have h := SignPatterns.fractional_phase_card_le fs gs (fun _ => 0) (fun _ => 0)
    Subtype.val (fun v : CoeffBox => windowMatrix features sigma epsilon v)
    (windowFamily features sigma epsilon) (25 * L ^ 2 + 5 * L)
    (by simpa only [zero_add] using hbound)
    (by intro G hG; exact (mem_filter.mp hG).2) (by simpa only [zero_add] using hdet)
  have hrank : Module.finrank ℝ CoeffVector = 36 := by
    simp [CoeffVector, Module.finrank_prod]
  simpa only [hrank, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    show 36 + 2 = 38 from rfl, show 36 + 1 = 37 from rfl] using h

abbrev Parities := Fin 2 × Fin 2 × Fin 2

def parityFlag (n : ℤ) : Bool := decide (n % 2 = 1)

def sigmaFlag {R b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (bits : Parities) (j : Fin R) (l : Fin b) : Bool :=
  parityFlag ((bits.1.val : ℤ) - bits.2.1.val * (j.val : ℤ) - (K : ℤ) * (j.val : ℤ) ^ 2 +
    bits.2.2.val * ((E j).val : ℤ) - delta l)

def windowFeature {R b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (bits : Parities) (j : Fin R) (l : Fin b) : Feature :=
  ![1, (j.val : ℤ), (j.val : ℤ) ^ 2, ((E j).val : ℤ),
    (delta l : ℤ) - if sigmaFlag K delta E bits j l then 1 else 0]

theorem windowFeature_bound {R b M : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (hd : ∀ l, delta l ≤ M) (E : Fin R → Fin (floorCap R + 1)) (bits : Parities)
    (j : Fin R) (l : Fin b) (i : Fin 5) :
    |windowFeature K delta E bits j l i| ≤ (floorCap R + M + 2 : ℕ) := by
  have hcap : R ^ 2 ≤ floorCap R := Nat.pow_le_pow_left (Nat.le_succ R) 2
  have hcap1 : 1 ≤ floorCap R := by
    simpa only [one_pow, floorCap] using Nat.pow_le_pow_left (show 1 ≤ R + 1 by omega) 2
  have hj : j.val ≤ R := j.isLt.le
  have hjsq : j.val ^ 2 ≤ floorCap R := (Nat.pow_le_pow_left hj 2).trans hcap
  have hjcap : j.val ≤ floorCap R := by
    have hR : R + 1 ≤ (R + 1) ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < R + 1 by omega) (show 1 ≤ 2 by decide)
    exact hj.trans ((Nat.le_succ R).trans hR)
  have hE : (E j).val ≤ floorCap R := Nat.le_of_lt_succ (E j).isLt
  have hdelta := hd l
  fin_cases i
  · change |(1 : ℤ)| ≤ (floorCap R + M + 2 : ℕ)
    norm_num
    omega
  · change |(j.val : ℤ)| ≤ (floorCap R + M + 2 : ℕ)
    simpa using (show (j.val : ℤ) ≤ (floorCap R + M + 2 : ℕ) by omega)
  · change |(j.val : ℤ) ^ 2| ≤ (floorCap R + M + 2 : ℕ)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact_mod_cast (show j.val ^ 2 ≤ floorCap R + M + 2 by omega)
  · change |((E j).val : ℤ)| ≤ (floorCap R + M + 2 : ℕ)
    simpa using (show ((E j).val : ℤ) ≤ (floorCap R + M + 2 : ℕ) by omega)
  · change |(delta l : ℤ) - if sigmaFlag K delta E bits j l then 1 else 0| ≤ (floorCap R + M + 2 : ℕ)
    split_ifs
    · apply abs_le.mpr
      constructor <;> omega
    · apply abs_le.mpr
      constructor <;> omega

def windowCountBound (R b L : ℕ) : ℕ :=
  (38 * (2 * (R * b * 2) * (2 * (25 * L ^ 2 + 5 * L) + 1) + 1) ^ 37) ^ 2

noncomputable def parityFamily {R b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (epsilon : Fin b → Bool) (E : Fin R → Fin (floorCap R + 1)) :
    Finset (Fin R → Finset (Fin b)) := by
  classical
  exact univ.biUnion fun bits : Parities =>
    windowFamily (windowFeature K delta E bits) (sigmaFlag K delta E bits) epsilon

theorem parityFamily_card_le {R b M : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (hd : ∀ l, delta l ≤ M) (epsilon : Fin b → Bool) (E : Fin R → Fin (floorCap R + 1)) :
    (parityFamily K delta epsilon E).card ≤ 8 * windowCountBound R b (floorCap R + M + 2) := by
  classical
  apply (card_biUnion_le_card_mul univ _ _ (fun bits _ =>
    windowFamily_card_le _ (windowFeature_bound K delta hd E bits) _ _)).trans_eq
  simp [Parities, windowCountBound]

noncomputable def allWindowFamily {b : ℕ} (K : ℕ) (delta : Fin b → ℕ) (epsilon : Fin b → Bool)
    (R : ℕ) : Finset (Fin R → Finset (Fin b)) := by
  classical
  exact (floorFamily R).biUnion (parityFamily K delta epsilon)

theorem allWindowFamily_card_le {R b M : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (hd : ∀ l, delta l ≤ M) (epsilon : Fin b → Bool) :
    (allWindowFamily K delta epsilon R).card ≤
      (floorFamily R).card * (8 * windowCountBound R b (floorCap R + M + 2)) := by
  classical
  exact card_biUnion_le_card_mul _ _ _ (fun E _ => parityFamily_card_le K delta hd epsilon E)

def planeScale (b C : ℕ) : ℕ := 4 * b * (2 * (25 * C ^ 2 + 5 * C) + 1) + 1

set_option exponentiation.threshold 1024 in
theorem windowCountBound_polynomial {R b L C : ℕ} (hR : 1 ≤ R) (hL : L ≤ C * R ^ 2) :
    windowCountBound R b L ≤ (1444 * planeScale b C ^ 74) * R ^ 370 := by
  have hR4 : 1 ≤ R ^ 4 := by simpa using Nat.pow_le_pow_left hR 4
  have hR5 : 1 ≤ R ^ 5 := by simpa using Nat.pow_le_pow_left hR 5
  have hR24 : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  have hL4 : L ≤ C * R ^ 4 := hL.trans (Nat.mul_le_mul_left _ hR24)
  have hL2 : L ^ 2 ≤ C ^ 2 * R ^ 4 := by
    calc
      L ^ 2 ≤ (C * R ^ 2) ^ 2 := Nat.pow_le_pow_left hL 2
      _ = _ := by rw [mul_pow, ← pow_mul]
  let B := 25 * L ^ 2 + 5 * L
  let F := 25 * C ^ 2 + 5 * C
  have hB : B ≤ F * R ^ 4 := by
    calc
      B ≤ 25 * (C ^ 2 * R ^ 4) + 5 * (C * R ^ 4) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hL2) (Nat.mul_le_mul_left _ hL4)
      _ = _ := by dsimp [F]; ring
  have hB' : 2 * B + 1 ≤ (2 * F + 1) * R ^ 4 := by
    calc
      2 * B + 1 ≤ 2 * (F * R ^ 4) + R ^ 4 := Nat.add_le_add (Nat.mul_le_mul_left _ hB) hR4
      _ = _ := by ring
  let q := 2 * (R * b * 2) * (2 * B + 1) + 1
  have hq : q ≤ planeScale b C * R ^ 5 := by
    calc
      q = (4 * R * b) * (2 * B + 1) + 1 := by dsimp [q]; ring
      _ ≤ (4 * R * b) * ((2 * F + 1) * R ^ 4) + R ^ 5 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hB') hR5
      _ = _ := by dsimp [planeScale, F]; ring
  have hid (x : ℕ) : (38 * x ^ 37) ^ 2 = 1444 * x ^ 74 := by ring
  calc
    windowCountBound R b L = 1444 * q ^ 74 := hid q
    _ ≤ 1444 * (planeScale b C * R ^ 5) ^ 74 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq 74)
    _ = (1444 * planeScale b C ^ 74) * R ^ 370 := by
      rw [mul_pow, ← pow_mul]
      exact (mul_assoc 1444 (planeScale b C ^ 74) (R ^ 370)).symm

def windowPolyConst (b M : ℕ) : ℕ := (25 * 10 ^ 8) * 8 * (1444 * planeScale b (M + 6) ^ 74)

theorem allWindowFamily_card_polynomial {R b M : ℕ} (hR : 1 ≤ R) (K : ℕ)
    (delta : Fin b → ℕ) (hd : ∀ l, delta l ≤ M) (epsilon : Fin b → Bool) :
    (allWindowFamily K delta epsilon R).card ≤ windowPolyConst b M * R ^ 394 := by
  have hR2 : 1 ≤ R ^ 2 := by simpa using Nat.pow_le_pow_left hR 2
  have hcap : floorCap R ≤ 4 * R ^ 2 := by unfold floorCap; nlinarith
  have hsmall : M + 2 ≤ (M + 2) * R ^ 2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left (M + 2) hR2
  have hL : floorCap R + M + 2 ≤ (M + 6) * R ^ 2 := by
    calc
      floorCap R + M + 2 = floorCap R + (M + 2) := by omega
      _ ≤ 4 * R ^ 2 + (M + 2) * R ^ 2 := Nat.add_le_add hcap hsmall
      _ = _ := by ring
  have hwindow := windowCountBound_polynomial (b := b) hR hL
  calc
    (allWindowFamily K delta epsilon R).card ≤
        (floorFamily R).card * (8 * windowCountBound R b (floorCap R + M + 2)) :=
      allWindowFamily_card_le K delta hd epsilon
    _ ≤ ((25 * 10 ^ 8) * R ^ 24) *
        (8 * ((1444 * planeScale b (M + 6) ^ 74) * R ^ 370)) :=
      Nat.mul_le_mul (floorFamily_card_polynomial hR) (Nat.mul_le_mul_left _ hwindow)
    _ = windowPolyConst b M * (R ^ 24 * R ^ 370) := by
      have hmul (a x y z : ℕ) : (a * x) * (8 * (y * z)) = (a * 8 * y) * (x * z) := by ring
      exact hmul (25 * 10 ^ 8) (R ^ 24) (1444 * planeScale b (M + 6) ^ 74) (R ^ 370)
    _ = windowPolyConst b M * R ^ 394 := by rw [← pow_add]

noncomputable def nonemptyWindowFamily {b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (epsilon : Fin b → Bool) (R : ℕ) : Finset (Fin R → Finset (Fin b)) := by
  classical
  exact (allWindowFamily K delta epsilon R).filter fun G => ∀ j, (G j).Nonempty

def rotation {R : ℕ} (s : Fin R) : Equiv.Perm (Fin R) :=
  letI := s.neZero
  Equiv.addLeft s

@[simp] theorem rotation_val {R : ℕ} (s j : Fin R) :
    (rotation s j).val = (s.val + j.val) % R := rfl

noncomputable def rotations (R : ℕ) : Finset (Equiv.Perm (Fin R)) := by
  classical
  exact univ.image rotation

theorem rotations_card_le (R : ℕ) : (rotations R).card ≤ R := by
  classical
  exact card_image_le.trans_eq (by simp)

/-- A single periodic word hits every nonempty window matrix in every cyclic position. -/
theorem exists_periodic_word {b M : ℕ} (hb : 1 < b) (K : ℕ) (delta : Fin b → ℕ)
    (hd : ∀ l, delta l ≤ M) (epsilon : Fin b → Bool) :
    ∃ R ≥ 2, ∃ w : Fin R → Fin b, ∀ s : Fin R,
      ∀ G ∈ nonemptyWindowFamily K delta epsilon R, ∃ j, w (rotation s j) ∈ G j := by
  classical
  obtain ⟨R, hbound, hR⟩ :=
    ((Bounty.polynomial_geometric_eventually_lt (windowPolyConst b M) 395 b hb).and
      (eventually_ge_atTop 2)).exists
  have hcard : (nonemptyWindowFamily K delta epsilon R).card ≤ windowPolyConst b M * R ^ 394 :=
    (card_filter_le _ _).trans (allWindowFamily_card_polynomial (by omega) K delta hd epsilon)
  have hsize : (rotations R).card * (nonemptyWindowFamily K delta epsilon R).card * (b - 1) ^ R < b ^ R := by
    calc
      _ ≤ R * (windowPolyConst b M * R ^ 394) * (b - 1) ^ R := by
        gcongr
        · exact rotations_card_le R
      _ = windowPolyConst b M * R ^ 395 * (b - 1) ^ R := by ring
      _ < _ := hbound
  obtain ⟨w, hw⟩ := Bounty.exists_hitting_word_permutations
    (nonemptyWindowFamily K delta epsilon R) (rotations R)
    (fun G hG => (mem_filter.mp hG).2) hsize
  refine ⟨R, hR, w, ?_⟩
  intro s G hG
  exact hw (rotation s) (mem_image.mpr ⟨s, mem_univ _, rfl⟩) G hG

def anchorRuler (r h : ℕ) : ℕ := 2 * r * h + h ^ 2 % r

def rulerNumerator (r h j : ℕ) : ℕ := h ^ 2 % r + 2 * h * j + j ^ 2

def rulerCarry (r h j : ℕ) : ℕ := rulerNumerator r h j / r

noncomputable def rulerFloorVector (r h : ℕ) : FloorVector :=
  ![((h ^ 2 % r : ℕ) : ℝ) / r, 2 * (h : ℝ) / r, 1 / (r : ℝ)]

theorem rulerFloorVector_inBox {r h : ℕ} (hr : 0 < r) (hh : h < r) :
    (0 ≤ rulerFloorVector r h 0 ∧ rulerFloorVector r h 0 ≤ 1) ∧
    (0 ≤ rulerFloorVector r h 1 ∧ rulerFloorVector r h 1 ≤ 2) ∧
    (0 ≤ rulerFloorVector r h 2 ∧ rulerFloorVector r h 2 ≤ 1) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : ((h ^ 2 % r : ℕ) : ℝ) ≤ r := by exact_mod_cast (Nat.mod_lt (h ^ 2) hr).le
  have hhR : (h : ℝ) ≤ r := by exact_mod_cast hh.le
  change (0 ≤ ((h ^ 2 % r : ℕ) : ℝ) / r ∧ ((h ^ 2 % r : ℕ) : ℝ) / r ≤ 1) ∧
    (0 ≤ 2 * (h : ℝ) / r ∧ 2 * (h : ℝ) / r ≤ 2) ∧ (0 ≤ 1 / (r : ℝ) ∧ 1 / (r : ℝ) ≤ 1)
  refine ⟨⟨by positivity, (div_le_one hrR).mpr hq⟩, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
  · apply (div_le_iff₀ hrR).mpr
    linarith
  · apply (div_le_one hrR).mpr
    exact_mod_cast (show 1 ≤ r by omega)

theorem rulerCarry_eq_floor (r h j : ℕ) :
    rulerCarry r h j = ⌊rulerPhase j (rulerFloorVector r h)⌋₊ := by
  have hphase : rulerPhase j (rulerFloorVector r h) = ((rulerNumerator r h j : ℕ) : ℝ) / r := by
    change ((h ^ 2 % r : ℕ) : ℝ) / r + (j : ℝ) * (2 * (h : ℝ) / r) +
      (j : ℝ) ^ 2 * (1 / (r : ℝ)) = ((rulerNumerator r h j : ℕ) : ℝ) / r
    unfold rulerNumerator
    push_cast
    ring
  rw [hphase, Nat.floor_div_eq_div]
  rfl

/-- Every actual quadratic-ruler carry vector occurs in the counted family. -/
theorem rulerCarry_mem_floorFamily {r h : ℕ} (hr : 0 < r) (hh : h < r) (R : ℕ) :
    ∃ E ∈ floorFamily R, ∀ j : Fin R, (E j).val = rulerCarry r h j.val := by
  classical
  let v : FloorBox := ⟨rulerFloorVector r h, rulerFloorVector_inBox hr hh⟩
  refine ⟨floorLabel R v, mem_filter.mpr ⟨mem_univ _, v, rfl⟩, ?_⟩
  intro j
  exact (rulerCarry_eq_floor r h j.val).symm

theorem anchorRuler_increment (r h j : ℕ) :
    (anchorRuler r (h + j) : ℤ) - anchorRuler r h =
      2 * (r + h : ℕ) * (j : ℤ) + (j : ℤ) ^ 2 - (r : ℤ) * rulerCarry r h j := by
  have hmod : (h + j) ^ 2 % r = rulerNumerator r h j % r := by
    unfold rulerNumerator
    rw [Nat.add_assoc, Nat.mod_add_mod]
    congr 1
    ring
  have hdiv := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mod_add_div (rulerNumerator r h j) r)
  unfold anchorRuler
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hmod]
  unfold rulerCarry rulerNumerator at *
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at *
  nlinarith

def parityOf (n : ℤ) : Fin 2 := ⟨(n % 2).toNat, by omega⟩

theorem parityOf_val (n : ℤ) : ((parityOf n).val : ℤ) = n % 2 := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg n (by decide))

theorem parityOf_modEq (n : ℤ) : Int.ModEq 2 ((parityOf n).val : ℤ) n := by
  change ((parityOf n).val : ℤ) % 2 = n % 2
  rw [parityOf_val, Int.emod_emod]

theorem sigmaFlag_actual {R b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (m A B : ℤ) (j : Fin R) (l : Fin b) :
    sigmaFlag K delta E (parityOf m, parityOf A, parityOf B) j l =
      parityFlag (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val - delta l) := by
  have h := (((parityOf_modEq m).sub ((parityOf_modEq A).mul (Int.ModEq.refl (j.val : ℤ)))).sub
    (Int.ModEq.refl ((K : ℤ) * (j.val : ℤ) ^ 2))).add
      ((parityOf_modEq B).mul (Int.ModEq.refl ((E j).val : ℤ)))
  have h' := h.sub (Int.ModEq.refl (delta l : ℤ))
  exact congrArg (fun n : ℤ => decide (n = 1)) h'

theorem parity_half_eq (n : ℤ) : 2 * ((n + n % 2) / 2) = n + n % 2 := by omega

theorem parityFlag_value (n : ℤ) : (if parityFlag n then (1 : ℤ) else 0) = n % 2 := by
  by_cases h : n % 2 = 1
  · simp [parityFlag, h]
  · simp [parityFlag, h]
    omega

noncomputable def fieldLinear {p : ℕ} (C : Fin 5 → ZMod p) (F : Feature) : ZMod p :=
  ∑ i, C i * (F i : ZMod p)

theorem fract_sum_residue {ι : Type*} [Fintype ι] {p : ℕ} (hp : 0 < p)
    (C : ι → ZMod p) (F : ι → ℤ) :
    Int.fract (∑ i, (F i : ℝ) * residueReal (C i)) =
      residueReal (∑ i, C i * (F i : ZMod p)) := by
  classical
  let : NeZero p := ⟨by omega⟩
  let z : ℤ := ∑ i, ((C i).val : ℤ) * F i
  have hreal : (∑ i, (F i : ℝ) * residueReal (C i)) = (z : ℝ) / p := by
    dsimp [z]
    push_cast
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro i _
    unfold residueReal
    ring
  have hcast : (z : ZMod p) = ∑ i, C i * (F i : ZMod p) := by
    simp [z]
  rw [hreal, fract_int_div_eq_residueReal hp z, hcast]

theorem fieldLinear_sq {p : ℕ} (C : Fin 5 → ZMod p) (F : Feature) :
    fieldLinear C F ^ 2 =
      ∑ ij : Fin 5 × Fin 5, (C ij.1 * C ij.2) * ((F ij.1 * F ij.2 : ℤ) : ZMod p) := by
  unfold fieldLinear
  rw [pow_two, sum_mul_sum, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  push_cast
  ring

noncomputable def normalizedCoeffs {p : ℕ} (C : Fin 5 → ZMod p) (H : Fin 5 → ℝ) (d : ℕ) : CoeffVector :=
  (fun i => residueReal (C i), (fun ij => residueReal (C ij.1 * C ij.2), (H, (d : ℝ) / p)))

theorem normalizedCoeffs_inBox {p : ℕ} (hp : 0 < p) (C : Fin 5 → ZMod p) (H : Fin 5 → ℝ) (d : ℕ) :
    (∀ i, 0 ≤ (normalizedCoeffs C H d).1 i ∧ (normalizedCoeffs C H d).1 i ≤ 1) ∧
    (∀ i, 0 ≤ (normalizedCoeffs C H d).2.1 i ∧ (normalizedCoeffs C H d).2.1 i ≤ 1) := by
  constructor <;> intro i <;> exact ⟨residueReal_nonneg _, (residueReal_lt_one hp _).le⟩

theorem normalized_linearPhase {p : ℕ} (hp : 0 < p) (C : Fin 5 → ZMod p)
    (H : Fin 5 → ℝ) (d : ℕ) (F : Feature) :
    Int.fract (linearPhase F (normalizedCoeffs C H d)) = residueReal (fieldLinear C F) :=
  fract_sum_residue hp C F

theorem normalized_squarePhase {p : ℕ} (hp : 0 < p) (C : Fin 5 → ZMod p)
    (H : Fin 5 → ℝ) (d : ℕ) (F : Feature) :
    Int.fract (squarePhase F (normalizedCoeffs C H d)) = residueReal (fieldLinear C F ^ 2) := by
  have h := fract_sum_residue hp (fun ij : Fin 5 × Fin 5 => C ij.1 * C ij.2)
    (fun ij => F ij.1 * F ij.2)
  rw [fieldLinear_sq]
  convert h using 1
  congr 1
  change (∑ ij : Fin 5 × Fin 5, (F ij.1 : ℝ) * (F ij.2 : ℝ) * residueReal (C ij.1 * C ij.2)) = _
  apply sum_congr rfl
  intro ij _
  push_cast
  rfl

theorem field_square_val {p : ℕ} (hp : 0 < p) (t : ZMod p) : (t ^ 2).val = t.val ^ 2 % p := by
  let : NeZero p := ⟨by omega⟩
  calc
    (t ^ 2).val = (((t.val ^ 2 : ℕ) : ZMod p)).val := by congr 1; simp
    _ = _ := ZMod.val_natCast _ _

noncomputable def arithmeticMatrix {R b p : ℕ} (features : Fin R → Fin b → Feature)
    (sigma : Fin R → Fin b → Bool) (epsilon : Fin b → Bool) (C : Fin 5 → ZMod p)
    (d : ℕ) (H : Fin R → Fin b → ℕ) : Fin R → Finset (Fin b) := by
  classical
  exact fun j => univ.filter fun l =>
    (((fieldLinear C (features j l)).val < d) ↔ sigma j l = true) ∧
    (((fieldLinear C (features j l)).val ^ 2 % p < H j l) ↔ epsilon l = true)

/-- The phase model agrees with the exact modular good-label predicates. -/
theorem arithmeticMatrix_eq_windowMatrix {R b p : ℕ} (hp : 0 < p)
    (features : Fin R → Fin b → Feature) (sigma : Fin R → Fin b → Bool)
    (epsilon : Fin b → Bool) (C : Fin 5 → ZMod p) (d : ℕ)
    (H : Fin R → Fin b → ℕ) (hc : Fin 5 → ℝ)
    (hH : ∀ j l, ∑ i, (features j l i : ℝ) * hc i = (H j l : ℝ) / p) :
    arithmeticMatrix features sigma epsilon C d H =
      windowMatrix features sigma epsilon (normalizedCoeffs C hc d) := by
  classical
  funext j
  ext l
  have ht := normalized_linearPhase hp C hc d (features j l)
  have hq := normalized_squarePhase hp C hc d (features j l)
  have hheight : heightPhase (features j l) (normalizedCoeffs C hc d) = (H j l : ℝ) / p := hH j l
  simp only [arithmeticMatrix, windowMatrix, mem_filter, mem_univ, true_and,
    ht, hq, hheight]
  change ((_ < d ↔ _) ∧ (_ < H j l ↔ _)) ↔
    ((residueReal (fieldLinear C (features j l)) < (d : ℝ) / p ↔ _) ∧
      (residueReal (fieldLinear C (features j l) ^ 2) < (H j l : ℝ) / p ↔ _))
  rw [residueReal_lt_div hp, residueReal_lt_div hp, field_square_val hp]

theorem arithmeticMatrix_mem_allWindowFamily {R b p : ℕ} (hp : 0 < p)
    (K : ℕ) (delta : Fin b → ℕ) (epsilon : Fin b → Bool)
    (E : Fin R → Fin (floorCap R + 1)) (hE : E ∈ floorFamily R) (bits : Parities)
    (C : Fin 5 → ZMod p) (d : ℕ) (H : Fin R → Fin b → ℕ) (hc : Fin 5 → ℝ)
    (hH : ∀ j l, ∑ i, (windowFeature K delta E bits j l i : ℝ) * hc i = (H j l : ℝ) / p) :
    arithmeticMatrix (windowFeature K delta E bits) (sigmaFlag K delta E bits) epsilon C d H ∈
      allWindowFamily K delta epsilon R := by
  classical
  apply mem_biUnion.mpr
  refine ⟨E, hE, mem_biUnion.mpr ⟨bits, mem_univ _, ?_⟩⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _, ⟨normalizedCoeffs C hc d, normalizedCoeffs_inBox hp C hc d⟩, ?_⟩
  exact (arithmeticMatrix_eq_windowMatrix hp _ _ _ C d H hc hH).symm

def sigmaValue (s : Bool) : ℤ := if s then 1 else 0

def dataNumerator {R b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (m A B : ℤ) (j : Fin R) (l : Fin b) : ℤ :=
  m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val - delta l

noncomputable def dataCoeffs {p : ℕ} (rho : ZMod p) (d K : ℕ) (m A B : ℤ) : Fin 5 → ZMod p :=
  ![rho * ((m : ZMod p) + 2 * (d : ZMod p) ^ 2), -rho * (A : ZMod p),
    -rho * (K : ZMod p), rho * (B : ZMod p), -rho]

noncomputable def dataHeightCoeffs (p K : ℕ) (m A B : ℤ) : Fin 5 → ℝ :=
  ![(m : ℝ) / (2 * p), -(A : ℝ) / (2 * p), -(K : ℝ) / (2 * p),
    (B : ℝ) / (2 * p), -1 / (2 * p)]

theorem sigmaValue_actual {R b : ℕ} (K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (m A B : ℤ) (j : Fin R) (l : Fin b) :
    sigmaValue (sigmaFlag K delta E (parityOf m, parityOf A, parityOf B) j l) =
      dataNumerator K delta E m A B j l % 2 := by
  rw [sigmaFlag_actual]
  exact parityFlag_value _

theorem fieldLinear_data {R b p : ℕ} (rho : ZMod p) (d K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (bits : Parities) (m A B : ℤ) (j : Fin R) (l : Fin b) :
    fieldLinear (dataCoeffs rho d K m A B) (windowFeature K delta E bits j l) =
      rho * ((dataNumerator K delta E m A B j l : ZMod p) +
        (sigmaValue (sigmaFlag K delta E bits j l) : ZMod p) + 2 * (d : ZMod p) ^ 2) := by
  by_cases hs : sigmaFlag K delta E bits j l = true
  · simp [fieldLinear, dataCoeffs, windowFeature, dataNumerator, sigmaValue, hs, Fin.sum_univ_succ]
    ring
  · simp [fieldLinear, dataCoeffs, windowFeature, dataNumerator, sigmaValue, hs, Fin.sum_univ_succ]
    ring

theorem heightPhase_data {R b : ℕ} (p K : ℕ) (delta : Fin b → ℕ)
    (E : Fin R → Fin (floorCap R + 1)) (bits : Parities) (m A B : ℤ) (j : Fin R) (l : Fin b) :
    heightPhase (windowFeature K delta E bits j l) (normalizedCoeffs (p := p) (fun _ => 0)
      (dataHeightCoeffs p K m A B) 0) =
      ((dataNumerator K delta E m A B j l + sigmaValue (sigmaFlag K delta E bits j l) : ℤ) : ℝ) /
        (2 * p) := by
  by_cases hs : sigmaFlag K delta E bits j l = true
  · simp [heightPhase_apply, normalizedCoeffs, dataHeightCoeffs, windowFeature,
      dataNumerator, sigmaValue, hs, Fin.sum_univ_succ]
    ring
  · simp [heightPhase_apply, normalizedCoeffs, dataHeightCoeffs, windowFeature,
      dataNumerator, sigmaValue, hs, Fin.sum_univ_succ]
    ring

/-- Every arithmetic window, with its three parity bits, lies in the finite counted family. -/
theorem dataMatrix_mem_allWindowFamily {R b p : ℕ} (hp : 0 < p)
    (rho : ZMod p) (d K : ℕ) (delta : Fin b → ℕ) (epsilon : Fin b → Bool)
    (E : Fin R → Fin (floorCap R + 1)) (hE : E ∈ floorFamily R) (m A B : ℤ)
    (H : Fin R → Fin b → ℕ)
    (hH : ∀ j l, 2 * (H j l : ℤ) = dataNumerator K delta E m A B j l +
      dataNumerator K delta E m A B j l % 2) :
    arithmeticMatrix (windowFeature K delta E (parityOf m, parityOf A, parityOf B))
      (sigmaFlag K delta E (parityOf m, parityOf A, parityOf B)) epsilon
      (dataCoeffs rho d K m A B) d H ∈ allWindowFamily K delta epsilon R := by
  apply arithmeticMatrix_mem_allWindowFamily hp K delta epsilon E hE _ _ d H (dataHeightCoeffs p K m A B)
  intro j l
  have hheight := heightPhase_data p K delta E (parityOf m, parityOf A, parityOf B) m A B j l
  rw [sigmaValue_actual, ← hH j l] at hheight
  change (∑ i, (windowFeature K delta E (parityOf m, parityOf A, parityOf B) j l i : ℝ) *
      dataHeightCoeffs p K m A B i) = _ at hheight
  rw [hheight]
  push_cast
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

theorem data_parameter_equation {R b p : ℕ} (hp : p.Prime) (rho : ZMod p) (d K : ℕ)
    (h2 : (2 : ZMod p) ≠ 0) (hrho : 4 * (d : ZMod p) * rho = 1)
    (delta : Fin b → ℕ) (E : Fin R → Fin (floorCap R + 1)) (m A B : ℤ)
    (H : Fin R → Fin b → ℕ)
    (hH : ∀ j l, 2 * (H j l : ℤ) = dataNumerator K delta E m A B j l +
      dataNumerator K delta E m A B j l % 2) (j : Fin R) (l : Fin b) :
    2 * (d : ZMod p) * fieldLinear (dataCoeffs rho d K m A B)
      (windowFeature K delta E (parityOf m, parityOf A, parityOf B) j l) =
        (H j l : ZMod p) + (d : ZMod p) ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hheight := hH j l
  rw [← sigmaValue_actual] at hheight
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) hheight
  push_cast at hc
  apply mul_left_cancel₀ h2
  calc
    _ = (4 * (d : ZMod p) * rho) *
        ((dataNumerator K delta E m A B j l : ZMod p) +
          (sigmaValue (sigmaFlag K delta E (parityOf m, parityOf A, parityOf B) j l) : ZMod p) +
          2 * (d : ZMod p) ^ 2) := by rw [fieldLinear_data]; ring
    _ = _ := by rw [hrho, one_mul, ← hc]; ring

theorem two_ne_zero {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
  · exact hp.ne_one h
  · exact hodd h

theorem twice_mul_ne_zero {p d : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) : 2 * (d : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  apply mul_ne_zero (two_ne_zero hp hodd)
  intro h
  have hm := (ZMod.natCast_eq_natCast_iff' d 0 p).mp (by simpa using h)
  simp only [Nat.mod_eq_of_lt hdp, Nat.zero_mod] at hm
  omega

theorem small_multiple_zero {P x y z : ℤ} (hP : 0 < P)
    (hx : -P < x ∧ x < P) (hy : -P < y ∧ y < P) (h : x - y = 2 * P * z) : z = 0 := by
  have hzhi : z < 1 := by
    by_contra! hz
    have hm := mul_le_mul_of_nonneg_left hz (by linarith : 0 ≤ 2 * P)
    nlinarith
  have hzlo : -1 < z := by
    by_contra! hz
    have hm := mul_le_mul_of_nonneg_left hz (by linarith : 0 ≤ 2 * P)
    nlinarith
  omega

/-- Exact integer difference coverage is equivalent to the two modular comparison tests. -/
theorem quadratic_difference_iff {p d H sigma epsilon : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) (hH0 : 0 < H) (hHp : H < p)
    (hsigma : sigma ≤ 1) (hepsilon : epsilon ≤ 1) (t : ZMod p)
    (ht : 2 * (d : ZMod p) * t = H + (d : ZMod p) ^ 2) :
    (∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (a : ℤ) - b = (d : ℤ) - (p : ℤ) * sigma + 2 * p * H - 2 * (p : ℤ) ^ 2 * epsilon) ↔
      ((t.val < d ↔ sigma = 1) ∧ (t.val ^ 2 % p < H ↔ epsilon = 1)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    have hu' : u < p := mem_range.mp hu
    have hv' : v < p := mem_range.mp hv
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have huZ : (0 : ℤ) ≤ u := Nat.cast_nonneg _
    have hvZ : (0 : ℤ) ≤ v := Nat.cast_nonneg _
    have huP : (u : ℤ) < p := by exact_mod_cast hu'
    have hvP : (v : ℤ) < p := by exact_mod_cast hv'
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd0
    have hdP : (d : ℤ) < p := by exact_mod_cast hdp
    have htarget : -(p : ℤ) < (d : ℤ) - (p : ℤ) * sigma ∧
        (d : ℤ) - (p : ℤ) * sigma < p := by
      interval_cases sigma <;> norm_num <;> omega
    let z : ℤ := (H : ℤ) - p * epsilon - (u ^ 2 % p : ℕ) + (v ^ 2 % p : ℕ)
    have hz : (u : ℤ) - v - ((d : ℤ) - (p : ℤ) * sigma) = 2 * p * z := by
      simp only [quadraticMark, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hab
      dsimp [z]
      push_cast at hab ⊢
      nlinarith
    have hz0 : z = 0 := small_multiple_zero hpZ (by constructor <;> omega) htarget hz
    have hdiff : (u : ℤ) - v = (d : ℤ) - (p : ℤ) * sigma := by rw [hz0] at hz; nlinarith
    have hsq : ((u ^ 2 % p : ℕ) : ℤ) - (v ^ 2 % p : ℕ) = (H : ℤ) - p * epsilon := by
      dsimp [z] at hz0
      push_cast at hz0 ⊢
      linarith
    have hdiffF : (u : ZMod p) - (v : ZMod p) = d := by
      have h := congrArg (fun n : ℤ => (n : ZMod p)) hdiff
      simp at h
      exact h.trans (sub_zero _)
    have hsqF : (u : ZMod p) ^ 2 - (v : ZMod p) ^ 2 = H := by
      have h := congrArg (fun n : ℤ => (n : ZMod p)) hsq
      simp at h
      exact h.trans (sub_zero _)
    have hvF : (v : ZMod p) = (u : ZMod p) - d := by linear_combination -hdiffF
    have huEq : 2 * (d : ZMod p) * u = H + (d : ZMod p) ^ 2 := by
      rw [hvF] at hsqF
      linear_combination hsqF
    have htu : t = (u : ZMod p) :=
      mul_left_cancel₀ (twice_mul_ne_zero hp hodd hd0 hdp) (ht.trans huEq.symm)
    have hval : t.val = u := by rw [htu, ZMod.val_natCast_of_lt hu']
    rw [hval]
    constructor
    · interval_cases sigma
      · norm_num only [Nat.cast_zero, mul_zero, sub_zero] at hdiff
        have huD : d ≤ u := by omega
        simp [not_lt.mpr huD]
      · norm_num only [Nat.cast_one, mul_one] at hdiff
        have huD : u < d := by omega
        simp [huD]
    · have hqu0 : (0 : ℤ) ≤ (u ^ 2 % p : ℕ) := Nat.cast_nonneg _
      have hqv0 : (0 : ℤ) ≤ (v ^ 2 % p : ℕ) := Nat.cast_nonneg _
      have hqvP : ((v ^ 2 % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt (v ^ 2) hp.pos
      interval_cases epsilon
      · norm_num only [Nat.cast_zero, mul_zero, sub_zero] at hsq
        have huH : H ≤ u ^ 2 % p := by omega
        simp [not_lt.mpr huH]
      · norm_num only [Nat.cast_one, mul_one] at hsq
        have huH : u ^ 2 % p < H := by omega
        simp [huH]
  · intro hgood
    have hsig : parameterSigma d t.val = sigma := by
      by_cases hlt : t.val < d
      · have hs := hgood.1.mp hlt
        simp [parameterSigma, hlt, hs]
      · have hs : sigma = 0 := by
          have hne : sigma ≠ 1 := fun h => hlt (hgood.1.mpr h)
          omega
        simp [parameterSigma, hlt, hs]
    have heps : parameterEpsilon p H t.val = epsilon := by
      by_cases hlt : t.val ^ 2 % p < H
      · have he := hgood.2.mp hlt
        simp [parameterEpsilon, hlt, he]
      · have he : epsilon = 0 := by
          have hne : epsilon ≠ 1 := fun h => hlt (hgood.2.mpr h)
          omega
        simp [parameterEpsilon, hlt, he]
    have ht' : 2 * (d : ZMod p) * t.val = H + (d : ZMod p) ^ 2 := by
      simpa only [ZMod.natCast_zmod_val] using ht
    have hc := quadratic_difference_canonical hp.pos hdp hH0 hHp (ZMod.val_lt t) ht'
    refine ⟨quadraticMark p t.val, mem_image.mpr ⟨t.val, mem_range.mpr (ZMod.val_lt t), rfl⟩,
      quadraticMark p (parameterPartner p d t.val),
      mem_image.mpr ⟨_, mem_range.mpr hc.1, rfl⟩, ?_⟩
    simpa only [hsig, heps] using hc.2

theorem parityOf_one_iff (n : ℤ) : (parityOf n).val = 1 ↔ parityFlag n = true := by
  change (n % 2).toNat = 1 ↔ decide (n % 2 = 1) = true
  simp only [decide_eq_true_eq]
  omega

/-- Membership in an arithmetic window matrix is exactly an integer blocking identity. -/
theorem data_entry_iff {R b p d : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) (rho : ZMod p) (hrho : 4 * (d : ZMod p) * rho = 1)
    (K : ℕ) (delta epsilon : Fin b → ℕ) (heps : ∀ l, epsilon l ≤ 1)
    (E : Fin R → Fin (floorCap R + 1)) (m A B : ℤ) (H : Fin R → Fin b → ℕ)
    (hH : ∀ j l, 2 * (H j l : ℤ) = dataNumerator K delta E m A B j l +
      dataNumerator K delta E m A B j l % 2)
    (hH0 : ∀ j l, 0 < H j l) (hHp : ∀ j l, H j l < p) (j : Fin R) (l : Fin b) :
    l ∈ arithmeticMatrix (windowFeature K delta E (parityOf m, parityOf A, parityOf B))
      (sigmaFlag K delta E (parityOf m, parityOf A, parityOf B)) (fun l => decide (epsilon l = 1))
      (dataCoeffs rho d K m A B) d H j ↔
      ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
        (d : ℤ) + (p : ℤ) * (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val) =
          a - b + (p : ℤ) * delta l + epsilon l * (2 * (p : ℤ) ^ 2) := by
  let t := fieldLinear (dataCoeffs rho d K m A B)
    (windowFeature K delta E (parityOf m, parityOf A, parityOf B) j l)
  let n := dataNumerator K delta E m A B j l
  let s := (parityOf n).val
  have hs : s ≤ 1 := Nat.le_of_lt_succ (parityOf n).isLt
  have hsflag : s = 1 ↔ sigmaFlag K delta E (parityOf m, parityOf A, parityOf B) j l = true := by
    rw [sigmaFlag_actual]
    exact parityOf_one_iff n
  have hpred : (l ∈ arithmeticMatrix (windowFeature K delta E (parityOf m, parityOf A, parityOf B))
      (sigmaFlag K delta E (parityOf m, parityOf A, parityOf B)) (fun l => decide (epsilon l = 1))
      (dataCoeffs rho d K m A B) d H j) ↔
      ((t.val < d ↔ s = 1) ∧ (t.val ^ 2 % p < H j l ↔ epsilon l = 1)) := by
    simp only [arithmeticMatrix, mem_filter, mem_univ, true_and, decide_eq_true_eq, hsflag]
    rfl
  have ht := data_parameter_equation hp rho d K (two_ne_zero hp hodd) hrho delta E m A B H hH j l
  have hdiff := quadratic_difference_iff hp hodd hd0 hdp (hH0 j l) (hHp j l) hs (heps l) t ht
  have hequiv (a b : ℕ) :
      ((d : ℤ) + (p : ℤ) * (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val) =
        a - b + (p : ℤ) * delta l + epsilon l * (2 * (p : ℤ) ^ 2)) ↔
      ((a : ℤ) - b = (d : ℤ) - (p : ℤ) * s + 2 * p * H j l - 2 * (p : ℤ) ^ 2 * epsilon l) := by
    have hh := hH j l
    rw [← parityOf_val n] at hh
    have hh' := congrArg (fun z : ℤ => (p : ℤ) * z) hh
    change (p : ℤ) * (2 * (H j l : ℤ)) = (p : ℤ) * (dataNumerator K delta E m A B j l + (s : ℤ)) at hh'
    unfold dataNumerator at hh'
    constructor <;> intro h <;> nlinarith [hh']
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hdiff.mpr (hpred.mp h)
    exact ⟨a, ha, b, hb, (hequiv a b).mpr hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact hpred.mpr (hdiff.mp ⟨a, ha, b, hb, (hequiv a b).mp hab⟩)

/-- A selected periodic word covers every admissible arithmetic window. -/
theorem periodic_word_data_cover {R b p d : ℕ} (w : Fin R → Fin b)
    (K : ℕ) (delta epsilon : Fin b → ℕ) (heps : ∀ l, epsilon l ≤ 1)
    (hw : ∀ s : Fin R, ∀ G ∈ nonemptyWindowFamily K delta (fun l => decide (epsilon l = 1)) R,
      ∃ j, w (rotation s j) ∈ G j)
    (hp : p.Prime) (hodd : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (rho : ZMod p) (hrho : 4 * (d : ZMod p) * rho = 1)
    (E : Fin R → Fin (floorCap R + 1)) (hE : E ∈ floorFamily R) (m A B : ℤ)
    (H : Fin R → Fin b → ℕ)
    (hH : ∀ j l, 2 * (H j l : ℤ) = dataNumerator K delta E m A B j l +
      dataNumerator K delta E m A B j l % 2)
    (hH0 : ∀ j l, 0 < H j l) (hHp : ∀ j l, H j l < p)
    (hcover : ∀ j : Fin R, ∃ l, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (d : ℤ) + (p : ℤ) * (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val) =
        a - b + (p : ℤ) * delta l + epsilon l * (2 * (p : ℤ) ^ 2))
    (s : Fin R) :
    ∃ j, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (d : ℤ) + (p : ℤ) * (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val) =
        a - b + (p : ℤ) * delta (w (rotation s j)) + epsilon (w (rotation s j)) * (2 * (p : ℤ) ^ 2) := by
  classical
  let G := arithmeticMatrix (windowFeature K delta E (parityOf m, parityOf A, parityOf B))
    (sigmaFlag K delta E (parityOf m, parityOf A, parityOf B)) (fun l => decide (epsilon l = 1))
    (dataCoeffs rho d K m A B) d H
  have hGall : G ∈ allWindowFamily K delta (fun l => decide (epsilon l = 1)) R :=
    dataMatrix_mem_allWindowFamily hp.pos rho d K delta _ E hE m A B H hH
  have hG : G ∈ nonemptyWindowFamily K delta (fun l => decide (epsilon l = 1)) R := by
    apply mem_filter.mpr
    refine ⟨hGall, ?_⟩
    intro j
    obtain ⟨l, hl⟩ := hcover j
    exact ⟨l, (data_entry_iff hp hodd hd0 hdp rho hrho K delta epsilon heps E m A B H hH hH0 hHp j l).mpr hl⟩
  obtain ⟨j, hj⟩ := hw s G hG
  exact ⟨j, (data_entry_iff hp hodd hd0 hdp rho hrho K delta epsilon heps E m A B H hH hH0 hHp
    j (w (rotation s j))).mp hj⟩

def baseQuotient (p K T r h : ℕ) : ℕ := K * anchorRuler r h + 4 * p + T

def baseline (p K T r h : ℕ) : ℕ := p * baseQuotient p K T r h

theorem baseQuotient_increment (p K T r h j : ℕ) :
    (baseQuotient p K T r (h + j) : ℤ) = baseQuotient p K T r h +
      ((2 * K * (r + h) : ℕ) : ℤ) * j + (K : ℤ) * (j : ℤ) ^ 2 -
        ((K * r : ℕ) : ℤ) * rulerCarry r h j := by
  have hi := anchorRuler_increment r h j
  unfold baseQuotient
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  linear_combination (K : ℤ) * hi

theorem window_value_identity (p K T r h x j : ℕ) :
    (x : ℤ) - baseline p K T r (h + j) =
      (x % p : ℕ) + (p : ℤ) * (((x / p : ℕ) : ℤ) - baseQuotient p K T r h -
        ((2 * K * (r + h) : ℕ) : ℤ) * j - (K : ℤ) * (j : ℤ) ^ 2 +
          ((K * r : ℕ) : ℤ) * rulerCarry r h j) := by
  have hi := baseQuotient_increment p K T r h j
  have hx := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mod_add_div x p)
  unfold baseline
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hi hx ⊢
  linear_combination -hx - (p : ℤ) * hi

def halfHeight (n : ℤ) : ℕ := ((n + n % 2) / 2).toNat

theorem height_from_interval {p d M y delta : ℕ} {m : ℤ} (hp : 0 < p) (hd : d < p)
    (hdelta : delta ≤ M) (hy : (y : ℤ) = d + (p : ℤ) * m)
    (hlo : 2 * p * (M + 2) ≤ y) (hhi : y < 2 * p * (p - 1)) :
    2 * (halfHeight (m - delta) : ℤ) = (m - delta) + (m - delta) % 2 ∧
      0 < halfHeight (m - delta) ∧ halfHeight (m - delta) < p := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hdZ : (d : ℤ) < p := by exact_mod_cast hd
  have hd0 : (0 : ℤ) ≤ d := Nat.cast_nonneg _
  have hdeltaZ : (delta : ℤ) ≤ M := by exact_mod_cast hdelta
  have hloZ : 2 * (p : ℤ) * ((M : ℤ) + 2) ≤ y := by exact_mod_cast hlo
  have hhiZ : (y : ℤ) < 2 * (p : ℤ) * ((p : ℤ) - 1) := by
    have h : (y : ℤ) < 2 * (p : ℤ) * ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hhi
    simpa only [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one] using h
  have hmlo : 2 * ((M : ℤ) + 2) ≤ m := by
    by_contra! h
    have h' : m ≤ 2 * ((M : ℤ) + 2) - 1 := by omega
    have hx := mul_le_mul_of_nonneg_left h' hpZ.le
    nlinarith
  have hmhi : m < 2 * ((p : ℤ) - 1) := by
    by_contra! h
    have hx := mul_le_mul_of_nonneg_left h hpZ.le
    nlinarith
  have hnlo : 0 < m - delta := by omega
  have hnhi : m - delta < 2 * ((p : ℤ) - 1) := by omega
  have heq := parity_half_eq (m - delta)
  have hqpos : 0 < ((m - delta) + (m - delta) % 2) / 2 := by omega
  have hqhi : ((m - delta) + (m - delta) % 2) / 2 < p := by omega
  have hcast : (halfHeight (m - delta) : ℤ) = ((m - delta) + (m - delta) % 2) / 2 :=
    Int.toNat_of_nonneg hqpos.le
  refine ⟨by rw [hcast]; exact heq, ?_, ?_⟩
  · omega
  · omega

theorem exists_inverse_four {p d : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : 0 < d) (hdp : d < p) : ∃ rho : ZMod p, 4 * (d : ZMod p) * rho = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 := two_ne_zero hp hodd
  have h2d := twice_mul_ne_zero hp hodd hd0 hdp
  have h4d : 4 * (d : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h2d using 1
    ring
  exact ⟨(4 * (d : ZMod p))⁻¹, mul_inv_cancel₀ h4d⟩

theorem rotation_mod_value {R : ℕ} (hR : 0 < R) (h : ℕ) (j : Fin R) :
    (rotation ⟨h % R, Nat.mod_lt h hR⟩ j).val = (h + j.val) % R := by
  rw [rotation_val, Nat.mod_add_mod]

/-- The periodic word covers every actual ruler window whose relative targets lie in the interior. -/
theorem ruler_window_cover {R b M : ℕ} (w : Fin R → Fin b)
    (K : ℕ) (delta epsilon : Fin b → ℕ) (hdelta : ∀ l, delta l ≤ M) (hepsilon : ∀ l, epsilon l ≤ 1)
    (hw : ∀ s : Fin R, ∀ G ∈ nonemptyWindowFamily K delta (fun l => decide (epsilon l = 1)) R,
      ∃ j, w (rotation s j) ∈ G j)
    (halphabet : ∀ (p y : ℕ), p.Prime → p ≠ 2 → 2 * p * (M + 2) ≤ y →
      y < 2 * p * (p - 1) → ¬ p ∣ y →
      ∃ l, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
        (y : ℤ) = a - b + (p : ℤ) * delta l + epsilon l * (2 * (p : ℤ) ^ 2))
    {p r h T x : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hr : 0 < r) (hh : h < r)
    (hbase : ∀ j : Fin R, baseline p K T r (h + j.val) ≤ x)
    (hlower : ∀ j : Fin R, 2 * p * (M + 2) ≤ x - baseline p K T r (h + j.val))
    (hupper : ∀ j : Fin R, x - baseline p K T r (h + j.val) < 2 * p * (p - 1))
    (hdiv : ¬ p ∣ x) (s : Fin R) :
    ∃ j, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (x : ℤ) = a - b + baseline p K T r (h + j.val) +
        (p : ℤ) * delta (w (rotation s j)) + epsilon (w (rotation s j)) * (2 * (p : ℤ) ^ 2) := by
  classical
  obtain ⟨E, hE, hEval⟩ := rulerCarry_mem_floorFamily hr hh R
  let d := x % p
  let m : ℤ := ((x / p : ℕ) : ℤ) - baseQuotient p K T r h
  let A : ℤ := (2 * K * (r + h) : ℕ)
  let B : ℤ := (K * r : ℕ)
  let raw (j : Fin R) : ℤ := m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val
  let H (j : Fin R) (l : Fin b) := halfHeight (dataNumerator K delta E m A B j l)
  have hdp : d < p := Nat.mod_lt _ hp.pos
  have hd0 : 0 < d := by
    have hdn : d ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
    omega
  have hy (j : Fin R) : ((x - baseline p K T r (h + j.val) : ℕ) : ℤ) = d + (p : ℤ) * raw j := by
    rw [Nat.cast_sub (hbase j)]
    have hi := window_value_identity p K T r h x j.val
    rw [← hEval j] at hi
    exact hi
  have hprops (j : Fin R) (l : Fin b) :
      2 * (H j l : ℤ) = dataNumerator K delta E m A B j l + dataNumerator K delta E m A B j l % 2 ∧
        0 < H j l ∧ H j l < p := by
    exact height_from_interval hp.pos hdp (hdelta l) (hy j) (hlower j) (hupper j)
  have hH : ∀ j l, 2 * (H j l : ℤ) = dataNumerator K delta E m A B j l +
      dataNumerator K delta E m A B j l % 2 := fun j l => (hprops j l).1
  have hH0 : ∀ j l, 0 < H j l := fun j l => (hprops j l).2.1
  have hHp : ∀ j l, H j l < p := fun j l => (hprops j l).2.2
  have hcover (j : Fin R) : ∃ l, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (d : ℤ) + (p : ℤ) * (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val) =
        a - b + (p : ℤ) * delta l + epsilon l * (2 * (p : ℤ) ^ 2) := by
    have hn : ¬ p ∣ x - baseline p K T r (h + j.val) := by
      intro hn
      apply hdiv
      have hb : p ∣ baseline p K T r (h + j.val) := dvd_mul_right _ _
      have hx := dvd_add hb hn
      simpa only [Nat.add_sub_of_le (hbase j)] using hx
    obtain ⟨l, a, ha, b, hb, he⟩ := halphabet p _ hp hodd (hlower j) (hupper j) hn
    exact ⟨l, a, ha, b, hb, (hy j).symm.trans he⟩
  obtain ⟨rho, hrho⟩ := exists_inverse_four hp hodd hd0 hdp
  obtain ⟨j, a, ha, b, hb, he⟩ := periodic_word_data_cover w K delta epsilon hepsilon hw hp hodd
    hd0 hdp rho hrho E hE m A B H hH hH0 hHp hcover s
  refine ⟨j, a, ha, b, hb, ?_⟩
  have hj := hy j
  rw [Nat.cast_sub (hbase j)] at hj
  change (x : ℤ) - baseline p K T r (h + j.val) =
    (d : ℤ) + (p : ℤ) * (m - A * j.val - (K : ℤ) * (j.val : ℤ) ^ 2 + B * (E j).val) at hj
  linarith

theorem exists_sparse_phase_word_ge_two :
    ∃ m ≥ 2, ∃ w : Fin m → Fin 6, ∀ v : PhaseBox, ∀ t : Fin 2,
      ∃ i, w i = phaseChoice (rulerIndex m i) t v := by
  classical
  have hne : ∀ m, ∀ G ∈ rulerFamily m, ∀ i, (G i).Nonempty := by
    intro m G hG i
    by_cases hm : m = 0
    · simp [rulerFamily, hm] at hG
    · simp only [rulerFamily, hm, ite_false, phaseFamilyAll, mem_biUnion, mem_univ,
        true_and] at hG
      obtain ⟨t, ht⟩ := hG
      exact phaseFamily_rows_nonempty _ t ht i
  have hc : ∀ m, (rulerFamily m).card ≤ (200 * 2048 ^ 18) * m ^ 126 := by
    intro m
    by_cases hm : m = 0
    · simp [rulerFamily, hm]
    · simpa only [rulerFamily, hm, ite_false] using phaseFamilyAll_card_polynomial (by omega : 1 ≤ m)
  obtain ⟨m, hm, w, hw⟩ := exists_hitting_word_of_polynomial_bound (by decide : 1 < 6)
    rulerFamily hne hc 2
  refine ⟨m, hm, w, ?_⟩
  intro v t
  have hmem : phaseMatrix (rulerIndex m) t v ∈ rulerFamily m := by
    simp only [rulerFamily, show m ≠ 0 by omega, ite_false, phaseFamilyAll, mem_biUnion,
      mem_univ, true_and]
    exact ⟨t, mem_filter.mpr ⟨mem_univ _, v, rfl⟩⟩
  obtain ⟨i, hi⟩ := hw _ hmem
  exact ⟨i, mem_singleton.mp hi⟩

/-- A finite alphabet with label uniqueness and uniform integer difference coverage. -/
structure CoverAlphabet where
  size : ℕ
  size_two : 2 ≤ size
  delta : Fin size → ℕ
  epsilon : Fin size → ℕ
  maxDelta : ℕ
  delta_le : ∀ i, delta i ≤ maxDelta
  epsilon_le : ∀ i, epsilon i ≤ 1
  pair_unique : ∀ i j k l, delta i + delta j = delta k + delta l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  covers : ∀ (p y : ℕ), p.Prime → p ≠ 2 → 2 * p * (maxDelta + 2) ≤ y →
    y < 2 * p * (p - 1) → ¬ p ∣ y →
    ∃ i, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (y : ℤ) = a - b + (p : ℤ) * delta i + epsilon i * (2 * (p : ℤ) ^ 2)

theorem exists_coverAlphabet : Nonempty CoverAlphabet := by
  obtain ⟨m, hm, w, hw⟩ := exists_sparse_phase_word_ge_two
  exact ⟨{
    size := m
    size_two := hm
    delta := alphabetDelta w
    epsilon := alphabetEpsilon w
    maxDelta := alphabetMax m
    delta_le := alphabetDelta_le (by omega) w
    epsilon_le := alphabetEpsilon_le w
    pair_unique := alphabetDelta_pair (by omega) w
    covers := fun p y hp hodd hlo hhi hdiv => sparse_word_covers (by omega) w hw hp hodd hlo hhi hdiv
  }⟩

theorem CoverAlphabet.exists_ruler_word (a : CoverAlphabet) (K : ℕ) :
    ∃ R ≥ 2, ∃ w : Fin R → Fin a.size, ∀ (p r h T x : ℕ),
      p.Prime → p ≠ 2 → 0 < r → h < r →
      (∀ j : Fin R, baseline p K T r (h + j.val) ≤ x) →
      (∀ j : Fin R, 2 * p * (a.maxDelta + 2) ≤ x - baseline p K T r (h + j.val)) →
      (∀ j : Fin R, x - baseline p K T r (h + j.val) < 2 * p * (p - 1)) →
      ¬ p ∣ x → ∀ s : Fin R,
      ∃ j, ∃ c ∈ quadraticSeed p, ∃ d ∈ quadraticSeed p,
        (x : ℤ) = c - d + baseline p K T r (h + j.val) +
          (p : ℤ) * a.delta (w (rotation s j)) + a.epsilon (w (rotation s j)) * (2 * (p : ℤ) ^ 2) := by
  obtain ⟨R, hR, w, hw⟩ := exists_periodic_word (by have := a.size_two; omega)
    K a.delta a.delta_le (fun i => decide (a.epsilon i = 1))
  refine ⟨R, hR, w, ?_⟩
  intro p r h T x hp hodd hr hh hbase hlo hhi hdiv s
  exact ruler_window_cover w K a.delta a.epsilon a.delta_le a.epsilon_le hw a.covers
    hp hodd hr hh hbase hlo hhi hdiv s

end Bounty.Window


/- Separated covering alphabets and tags for the anchor construction. -/

namespace Bounty.Construction

open Finset Filter Window

def phasePolyConstant (C : ℕ) : ℕ := 200 * (16 * (C + 1) ^ 2) ^ 18

theorem phaseFamilyAll_card_scaled {m C : ℕ} (hm : 1 ≤ m)
    (k : Fin m → ℕ) (hk : ∀ i, k i ≤ C * m ^ 3) :
    (phaseFamilyAll k).card ≤ phasePolyConstant C * m ^ 126 := by
  let D := (C + 1) ^ 2
  let B := 1 + C * m ^ 3 + (C * m ^ 3) ^ 2
  let q := 2 * (m * 2) * (2 * B + 1) + 1
  have hm6 : 1 ≤ m ^ 6 := by simpa using Nat.pow_le_pow_left hm 6
  have hm7 : 1 ≤ m ^ 7 := by simpa using Nat.pow_le_pow_left hm 7
  have hm36 : m ^ 3 ≤ m ^ 6 := Nat.pow_le_pow_right hm (by decide)
  have hD : 1 ≤ D := by
    simpa only [D, one_pow] using Nat.pow_le_pow_left (show 1 ≤ C + 1 by omega) 2
  have hB : B ≤ D * m ^ 6 := by
    calc
      B = 1 + C * m ^ 3 + C ^ 2 * m ^ 6 := by dsimp [B]; rw [mul_pow, ← pow_mul]
      _ ≤ m ^ 6 + C * m ^ 6 + C ^ 2 * m ^ 6 :=
        Nat.add_le_add_right (Nat.add_le_add hm6 (Nat.mul_le_mul_left C hm36)) _
      _ = (1 + C + C ^ 2) * m ^ 6 := by ring
      _ ≤ D * m ^ 6 := Nat.mul_le_mul_right _ (by dsimp [D]; nlinarith)
  have hDm : 1 ≤ D * m ^ 6 := by simpa using Nat.mul_le_mul hD hm6
  have hB' : 2 * B + 1 ≤ 3 * D * m ^ 6 := by
    calc
      2 * B + 1 ≤ 2 * (D * m ^ 6) + D * m ^ 6 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hB) hDm
      _ = _ := by ring
  have hq : q ≤ (16 * D) * m ^ 7 := by
    calc
      q = 4 * m * (2 * B + 1) + 1 := by dsimp [q]; ring
      _ ≤ 4 * m * (3 * D * m ^ 6) + m ^ 7 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hB') hm7
      _ = 12 * D * m ^ 7 + m ^ 7 := by ring
      _ ≤ 12 * D * m ^ 7 + D * m ^ 7 :=
        Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right (m ^ 7) hD) _
      _ ≤ (16 * D) * m ^ 7 := by nlinarith
  have hc : (phaseFamilyAll k).card ≤ 2 * (10 * q ^ 9) ^ 2 := phaseFamilyAll_card_le k hk
  have hid (n : ℕ) : 2 * (10 * n ^ 9) ^ 2 = 200 * n ^ 18 := by ring
  calc
    (phaseFamilyAll k).card ≤ 200 * q ^ 18 := by simpa only [hid] using hc
    _ ≤ 200 * ((16 * D) * m ^ 7) ^ 18 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq 18)
    _ = phasePolyConstant C * m ^ 126 := by
      rw [mul_pow, ← pow_mul]
      exact (mul_assoc 200 ((16 * D) ^ 18) (m ^ 126)).symm

def scaledIndex (s m : ℕ) (i : Fin m) : ℕ := s * rulerValue m i.val

theorem scaledIndex_le {s m : ℕ} (hm : 1 ≤ m) (i : Fin m) :
    scaledIndex s m i ≤ (3 * s) * m ^ 3 := by
  have hi : i.val ≤ m := i.isLt.le
  have hm3 : m ≤ m ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hm (show 1 ≤ 3 by decide)
  calc
    scaledIndex s m i ≤ s * (m ^ 3 + 2 * m * m ^ 2) := by
      unfold scaledIndex rulerValue
      gcongr
      exact hi.trans hm3
    _ = (3 * s) * m ^ 3 := by ring

noncomputable def scaledFamily (s m : ℕ) : Finset (Fin m → Finset (Fin 6)) :=
  if m = 0 then ∅ else phaseFamilyAll (scaledIndex s m)

theorem exists_scaled_phase_word (s : ℕ) :
    ∃ m ≥ 2, ∃ w : Fin m → Fin 6, ∀ v : PhaseBox, ∀ t : Fin 2,
      ∃ i, w i = phaseChoice (scaledIndex s m i) t v := by
  classical
  have hne : ∀ m, ∀ G ∈ scaledFamily s m, ∀ i, (G i).Nonempty := by
    intro m G hG i
    by_cases hm : m = 0
    · simp [scaledFamily, hm] at hG
    · simp only [scaledFamily, hm, ite_false, phaseFamilyAll, mem_biUnion, mem_univ, true_and] at hG
      obtain ⟨t, ht⟩ := hG
      exact phaseFamily_rows_nonempty _ t ht i
  have hc : ∀ m, (scaledFamily s m).card ≤ phasePolyConstant (3 * s) * m ^ 126 := by
    intro m
    by_cases hm : m = 0
    · simp [scaledFamily, hm]
    · simpa only [scaledFamily, hm, ite_false] using
        phaseFamilyAll_card_scaled (by omega : 1 ≤ m) (scaledIndex s m) (scaledIndex_le (by omega))
  obtain ⟨m, hm, w, hw⟩ := exists_hitting_word_of_polynomial_bound (by decide : 1 < 6)
    (scaledFamily s) hne hc 2
  refine ⟨m, hm, w, ?_⟩
  intro v t
  have hmem : phaseMatrix (scaledIndex s m) t v ∈ scaledFamily s m := by
    simp only [scaledFamily, show m ≠ 0 by omega, ite_false, phaseFamilyAll, mem_biUnion,
      mem_univ, true_and]
    exact ⟨t, mem_filter.mpr ⟨mem_univ _, v, rfl⟩⟩
  obtain ⟨i, hi⟩ := hw _ hmem
  exact ⟨i, mem_singleton.mp hi⟩

def scaledDelta {m : ℕ} (s : ℕ) (w : Fin m → Fin 6) (i : Fin m) : ℕ :=
  2 * scaledIndex s m i + (w i).val / 2

def scaledMax (s m : ℕ) : ℕ := 6 * s * m ^ 3 + 2

theorem scaledDelta_le {s m : ℕ} (hm : 1 ≤ m) (w : Fin m → Fin 6) (i : Fin m) :
    scaledDelta s w i ≤ scaledMax s m := by
  have hi := scaledIndex_le (s := s) hm i
  have hw := (w i).isLt
  unfold scaledDelta scaledMax
  nlinarith [show (w i).val / 2 ≤ 2 by omega]

theorem word_cover_from_index_bound {m M : ℕ} (k : Fin m → ℕ) (w : Fin m → Fin 6)
    (hw : ∀ v : PhaseBox, ∀ t : Fin 2, ∃ i, w i = phaseChoice (k i) t v)
    (hk : ∀ i, k i ≤ M) {p y : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hlower : 2 * p * (M + 2) ≤ y) (hupper : y < 2 * p * (p - 1)) (hdiv : ¬ p ∣ y) :
    ∃ i, ∃ a ∈ quadraticSeed p, ∃ b ∈ quadraticSeed p,
      (y : ℤ) = a - b + (p : ℤ) * ((2 * k i + (w i).val / 2 : ℕ) : ℤ) +
        (alphabetEpsilon w i : ℤ) * (2 * (p : ℤ) ^ 2) := by
  let d := y % p
  let q := y / p
  let Y := q / 2
  let t : Fin 2 := ⟨q % 2, Nat.mod_lt _ (by decide)⟩
  have hp2 : 0 < 2 * p := Nat.mul_pos (by decide) hp.pos
  have hYeq : Y = y / (2 * p) := by
    dsimp [Y, q]
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p 2]
  have hYlo : M + 2 ≤ Y := by
    rw [hYeq]
    apply (Nat.le_div_iff_mul_le hp2).mpr
    nlinarith
  have hY : Y < p := by
    rw [hYeq]
    have h : y / (2 * p) < p - 1 := (Nat.div_lt_iff_lt_mul hp2).mpr (by nlinarith)
    omega
  have hdp : d < p := Nat.mod_lt _ hp.pos
  have hd0 : 0 < d := by
    have hdne : d ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
    omega
  have hkY : ∀ i, k i < Y := fun i => by have := hk i; omega
  have hy : y = d + p * t.val + 2 * p * Y := by
    have hq : q = q % 2 + 2 * (q / 2) := (Nat.mod_add_div q 2).symm
    calc
      y = d + p * q := (Nat.mod_add_div y p).symm
      _ = d + p * (q % 2 + 2 * (q / 2)) := congrArg (fun n => d + p * n) hq
      _ = _ := by dsimp [t, Y]; ring
  obtain ⟨i, a, ha, b, hb, he⟩ := phase_word_covers_decomposed k w hw hp hodd hd0 hdp hY hkY t
  refine ⟨i, a, ha, b, hb, ?_⟩
  have hyZ : (y : ℤ) = (d : ℤ) + (p : ℤ) * t.val + 2 * p * Y := by exact_mod_cast hy
  exact hyZ.trans he

theorem scaledDelta_gap {G s m : ℕ} (hm : 1 ≤ m) (hs : G + 4 < 2 * s)
    (w : Fin m → Fin 6) (i j k l : Fin m)
    (hne : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    (G : ℤ) < |((scaledDelta s w i : ℤ) + scaledDelta s w j) -
      ((scaledDelta s w k : ℤ) + scaledDelta s w l)| := by
  let q : ℤ := (rulerValue m i.val : ℤ) + rulerValue m j.val -
    ((rulerValue m k.val : ℤ) + rulerValue m l.val)
  let e : ℤ := (((w i).val / 2 : ℕ) : ℤ) + ((w j).val / 2 : ℕ) -
    ((((w k).val / 2 : ℕ) : ℤ) + ((w l).val / 2 : ℕ))
  have hq : q ≠ 0 := by
    intro hq0
    have hbase : rulerValue m i.val + rulerValue m j.val = rulerValue m k.val + rulerValue m l.val := by
      dsimp [q] at hq0
      omega
    rcases rulerValue_pair (by omega) i.isLt j.isLt k.isLt l.isLt hbase with h | h
    · exact hne (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)
    · exact hne (Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩)
  have he : -4 ≤ e ∧ e ≤ 4 := by
    have hi := (w i).isLt
    have hj := (w j).isLt
    have hk := (w k).isLt
    have hl := (w l).isLt
    dsimp [e]
    omega
  have hdiff : ((scaledDelta s w i : ℤ) + scaledDelta s w j) -
      ((scaledDelta s w k : ℤ) + scaledDelta s w l) = 2 * (s : ℤ) * q + e := by
    dsimp [scaledDelta, scaledIndex, q, e]
    ring
  rw [hdiff]
  by_contra! h
  have hb := abs_le.mp h
  have hsZ : (G : ℤ) + 4 < 2 * (s : ℤ) := by exact_mod_cast hs
  rcases (show q ≤ -1 ∨ 1 ≤ q by omega) with hneg | hpos
  · have hp := mul_le_mul_of_nonneg_left hneg (show 0 ≤ 2 * (s : ℤ) by positivity)
    nlinarith
  · have hp := mul_le_mul_of_nonneg_left hpos (show 0 ≤ 2 * (s : ℤ) by positivity)
    nlinarith

structure SeparatedAlphabet (G : ℕ) extends CoverAlphabet where
  gap_lt : ∀ i j k l, ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
    (G : ℤ) < |((delta i : ℤ) + delta j) - ((delta k : ℤ) + delta l)|

/-- The covering alphabet can have arbitrarily separated nontrivial pair sums. -/
theorem exists_separatedAlphabet (G : ℕ) : Nonempty (SeparatedAlphabet G) := by
  let s := G + 4
  obtain ⟨m, hm, w, hw⟩ := exists_scaled_phase_word s
  have hs : G + 4 < 2 * s := by dsimp [s]; omega
  have hgap := scaledDelta_gap (by omega : 1 ≤ m) hs w
  have hpairs : ∀ i j k l, scaledDelta s w i + scaledDelta s w j = scaledDelta s w k + scaledDelta s w l →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    intro i j k l heq
    by_contra hne
    have hg := hgap i j k l hne
    have hz : ((scaledDelta s w i : ℤ) + scaledDelta s w j) -
        ((scaledDelta s w k : ℤ) + scaledDelta s w l) = 0 := by
      have hc := congrArg (fun n : ℕ => (n : ℤ)) heq
      push_cast at hc
      linarith
    rw [hz, abs_zero] at hg
    exact (not_lt_of_ge (Int.natCast_nonneg G)) hg
  have hindex : ∀ i, scaledIndex s m i ≤ scaledMax s m := by
    intro i
    have hi := scaledIndex_le (s := s) (by omega : 1 ≤ m) i
    unfold scaledMax
    nlinarith
  exact ⟨{
    size := m
    size_two := hm
    delta := scaledDelta s w
    epsilon := alphabetEpsilon w
    maxDelta := scaledMax s m
    delta_le := scaledDelta_le (by omega) w
    epsilon_le := alphabetEpsilon_le w
    pair_unique := hpairs
    covers := fun p y hp hodd hlo hhi hdiv => by
      simpa only [scaledDelta] using word_cover_from_index_bound (scaledIndex s m) w hw hindex hp hodd hlo hhi hdiv
    gap_lt := hgap
  }⟩


def deltaDiff (a : CoverAlphabet) (i j k l : Fin a.size) : ℤ :=
  (a.delta i : ℤ) + a.delta j - ((a.delta k : ℤ) + a.delta l)

def epsilonDiff (a : CoverAlphabet) (i j k l : Fin a.size) : ℤ :=
  (a.epsilon i : ℤ) + a.epsilon j - ((a.epsilon k : ℤ) + a.epsilon l)

def tag {K : ℕ} (a : CoverAlphabet) (p : ℕ) (i : Fin a.size) : ZMod K :=
  (a.delta i : ZMod K) + 2 * (p : ZMod K) * (a.epsilon i : ZMod K)

def TagPairUnique (K p : ℕ) (a : CoverAlphabet) : Prop :=
  ∀ i j k l, tag (K := K) a p i + tag a p j = tag a p k + tag a p l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k)

theorem deltaDiff_abs_le (a : CoverAlphabet) (i j k l : Fin a.size) :
    |deltaDiff a i j k l| ≤ 2 * (a.maxDelta : ℤ) := by
  have hi := a.delta_le i
  have hj := a.delta_le j
  have hk := a.delta_le k
  have hl := a.delta_le l
  apply abs_le.mpr
  unfold deltaDiff
  constructor <;> omega

theorem epsilonDiff_abs_le (a : CoverAlphabet) (i j k l : Fin a.size) :
    |epsilonDiff a i j k l| ≤ 2 := by
  have hi := a.epsilon_le i
  have hj := a.epsilon_le j
  have hk := a.epsilon_le k
  have hl := a.epsilon_le l
  apply abs_le.mpr
  unfold epsilonDiff
  constructor <;> omega

theorem deltaDiff_ne_zero (a : CoverAlphabet) (i j k l : Fin a.size)
    (hne : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) : deltaDiff a i j k l ≠ 0 := by
  intro h
  have heq : a.delta i + a.delta j = a.delta k + a.delta l := by
    unfold deltaDiff at h
    omega
  exact hne (a.pair_unique i j k l heq)

theorem tag_collision_divides {K p : ℕ} (a : CoverAlphabet) (i j k l : Fin a.size)
    (h : tag (K := K) a p i + tag a p j = tag a p k + tag a p l) :
    (K : ℤ) ∣ deltaDiff a i j k l + 2 * (p : ℤ) * epsilonDiff a i j k l := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ K).mp
  unfold tag at h
  unfold deltaDiff epsilonDiff
  push_cast
  linear_combination h

theorem int_eq_zero_of_dvd_abs_lt {K : ℕ} {z : ℤ} (hdvd : (K : ℤ) ∣ z)
    (habs : |z| < (K : ℤ)) : z = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  have hz : (z.natAbs : ℤ) < K := by simpa only [Int.natCast_natAbs] using habs
  have h : z.natAbs < K := by exact_mod_cast hz
  simpa using h

/-- Two separated alphabets cannot both have a tag collision at the same residue. -/
theorem one_of_two_tag_unique (a : CoverAlphabet) (b : SeparatedAlphabet (4 * a.maxDelta))
    {K : ℕ} (hK : 4 * (a.maxDelta + b.maxDelta) < K) (p : ℕ) :
    TagPairUnique K p a ∨ TagPairUnique K p b.toCoverAlphabet := by
  classical
  by_contra hboth
  obtain ⟨ha, hb⟩ := not_or.mp hboth
  simp only [TagPairUnique, not_forall] at ha hb
  obtain ⟨i₁, j₁, k₁, l₁, h₁, hn₁⟩ := ha
  obtain ⟨i₂, j₂, k₂, l₂, h₂, hn₂⟩ := hb
  let d₁ := deltaDiff a i₁ j₁ k₁ l₁
  let d₂ := deltaDiff b.toCoverAlphabet i₂ j₂ k₂ l₂
  let e₁ := epsilonDiff a i₁ j₁ k₁ l₁
  let e₂ := epsilonDiff b.toCoverAlphabet i₂ j₂ k₂ l₂
  have hd₁ : |d₁| ≤ 2 * (a.maxDelta : ℤ) := deltaDiff_abs_le _ _ _ _ _
  have hd₂ : |d₂| ≤ 2 * (b.maxDelta : ℤ) := deltaDiff_abs_le _ _ _ _ _
  have he₁ : |e₁| ≤ 2 := epsilonDiff_abs_le _ _ _ _ _
  have he₂ : |e₂| ≤ 2 := epsilonDiff_abs_le _ _ _ _ _
  have hz₁ : (K : ℤ) ∣ d₁ + 2 * (p : ℤ) * e₁ := tag_collision_divides _ _ _ _ _ h₁
  have hz₂ : (K : ℤ) ∣ d₂ + 2 * (p : ℤ) * e₂ := tag_collision_divides _ _ _ _ _ h₂
  have hKZ : 4 * ((a.maxDelta : ℤ) + b.maxDelta) < K := by exact_mod_cast hK
  have he₁ne : e₁ ≠ 0 := by
    intro he
    rw [he, mul_zero, add_zero] at hz₁
    have hzero := int_eq_zero_of_dvd_abs_lt hz₁ (lt_of_le_of_lt hd₁ (by omega))
    exact deltaDiff_ne_zero a i₁ j₁ k₁ l₁ hn₁ hzero
  have hcrossdvd : (K : ℤ) ∣ e₂ * d₁ - e₁ * d₂ := by
    have h := dvd_sub (dvd_mul_of_dvd_right hz₁ e₂) (dvd_mul_of_dvd_right hz₂ e₁)
    convert h using 1
    ring
  have hcrossbound : |e₂ * d₁ - e₁ * d₂| ≤ 4 * ((a.maxDelta : ℤ) + b.maxDelta) := by
    calc
      |e₂ * d₁ - e₁ * d₂| ≤ |e₂ * d₁| + |e₁ * d₂| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (e₂ * d₁) (-(e₁ * d₂))
      _ = |e₂| * |d₁| + |e₁| * |d₂| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * (2 * (a.maxDelta : ℤ)) + 2 * (2 * (b.maxDelta : ℤ)) := by
        exact add_le_add (mul_le_mul he₂ hd₁ (abs_nonneg _) (by positivity))
          (mul_le_mul he₁ hd₂ (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hcross := int_eq_zero_of_dvd_abs_lt hcrossdvd (lt_of_le_of_lt hcrossbound hKZ)
  have hprod : |e₁| * |d₂| = |e₂| * |d₁| := by
    have h : e₁ * d₂ = e₂ * d₁ := by omega
    simpa only [abs_mul] using congrArg abs h
  have he₁pos : 1 ≤ |e₁| := by have := abs_pos.mpr he₁ne; omega
  have hlo : |d₂| ≤ |e₁| * |d₂| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he₁pos (abs_nonneg d₂)
  have hhi : |e₂| * |d₁| ≤ 4 * (a.maxDelta : ℤ) := by
    have h := mul_le_mul he₂ hd₁ (abs_nonneg _) (by positivity : (0 : ℤ) ≤ 2)
    nlinarith
  have hgap0 : ((4 * a.maxDelta : ℕ) : ℤ) < |d₂| := b.gap_lt i₂ j₂ k₂ l₂ hn₂
  have hgap : 4 * (a.maxDelta : ℤ) < |d₂| := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgap0
  linarith


theorem exists_sumfree_translate {K b : ℕ} (hK : b ^ 3 < K) (v : Fin b → ZMod K) :
    ∃ T : ZMod K, ∀ i j k, (T + v i) + (T + v j) ≠ T + v k := by
  classical
  let : NeZero K := ⟨by omega⟩
  let bad : Finset (ZMod K) := (univ : Finset ((Fin b × Fin b) × Fin b)).image
    (fun q => v q.2 - v q.1.1 - v q.1.2)
  have hbad : bad.card ≤ b ^ 3 := by
    have h := card_image_le (s := (univ : Finset ((Fin b × Fin b) × Fin b)))
      (f := fun q => v q.2 - v q.1.1 - v q.1.2)
    simpa only [card_univ, Fintype.card_prod, Fintype.card_fin, pow_succ, pow_zero, mul_one, one_mul] using h
  have hout : ∃ T : ZMod K, T ∉ bad := by
    by_contra! h
    have hs : (univ : Finset (ZMod K)) ⊆ bad := fun T _ => h T
    have hc := card_le_card hs
    have hcard : (univ : Finset (ZMod K)).card = K := by simp
    rw [hcard] at hc
    omega
  obtain ⟨T, hT⟩ := hout
  refine ⟨T, ?_⟩
  intro i j k h
  apply hT
  apply mem_image.mpr
  refine ⟨((i, j), k), mem_univ _, ?_⟩
  linear_combination -h

def anchorOffset (a : CoverAlphabet) (p T : ℕ) (i : Fin a.size) : ℕ :=
  4 * p + T + a.delta i + 2 * p * a.epsilon i

structure TagWitness (a : CoverAlphabet) (K p : ℕ) where
  shift : ℕ
  shift_lt : shift < K
  pairs : ∀ i j k l,
    (anchorOffset a p shift i : ZMod K) + anchorOffset a p shift j =
      (anchorOffset a p shift k : ZMod K) + anchorOffset a p shift l →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  sum_free : ∀ i j k, (anchorOffset a p shift i : ZMod K) + anchorOffset a p shift j ≠
    (anchorOffset a p shift k : ZMod K)

theorem exists_tagWitness {K p : ℕ} (a : CoverAlphabet) (hK : a.size ^ 3 < K)
    (hpairs : TagPairUnique K p a) : Nonempty (TagWitness a K p) := by
  let : NeZero K := ⟨by have := a.size_two; omega⟩
  obtain ⟨T, hT⟩ := exists_sumfree_translate hK (tag (K := K) a p)
  let shift := (T - 4 * (p : ZMod K)).val
  have hshift : (shift : ZMod K) = T - 4 * (p : ZMod K) := ZMod.natCast_zmod_val _
  have hoff (i : Fin a.size) : (anchorOffset a p shift i : ZMod K) = T + tag a p i := by
    unfold anchorOffset tag
    push_cast
    rw [hshift]
    ring
  refine ⟨⟨shift, ZMod.val_lt _, ?_, ?_⟩⟩
  · intro i j k l h
    apply hpairs i j k l
    simp only [hoff] at h
    linear_combination h
  · intro i j k
    simpa only [hoff] using hT i j k

theorem exists_two_tagged_alphabets :
    ∃ a b : CoverAlphabet, ∃ K : ℕ, 0 < K ∧
      ∀ p : ℕ, Nonempty (TagWitness a K p) ∨ Nonempty (TagWitness b K p) := by
  obtain ⟨a⟩ := Window.exists_coverAlphabet
  obtain ⟨b⟩ := exists_separatedAlphabet (4 * a.maxDelta)
  let K := 4 * (a.maxDelta + b.maxDelta) + a.size ^ 3 + b.size ^ 3 + 1
  have hK : 4 * (a.maxDelta + b.maxDelta) < K := by dsimp [K]; omega
  have hKa : a.size ^ 3 < K := by dsimp [K]; omega
  have hKb : b.size ^ 3 < K := by dsimp [K]; omega
  refine ⟨a, b.toCoverAlphabet, K, by dsimp [K]; omega, ?_⟩
  intro p
  rcases one_of_two_tag_unique a b hK p with ha | hb
  · exact Or.inl (exists_tagWitness a hKa ha)
  · exact Or.inr (exists_tagWitness b.toCoverAlphabet hKb hb)

end Bounty.Construction


namespace Bounty.Construction

open Finset Filter Window

theorem anchorRuler_pair {r i j k l : ℕ} (hr : r.Prime) (hodd : r ≠ 2)
    (hi : i < r) (hj : j < r) (hk : k < r) (hl : l < r)
    (h : anchorRuler r i + anchorRuler r j = anchorRuler r k + anchorRuler r l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hqi := Nat.mod_lt (i ^ 2) hr.pos
  have hqj := Nat.mod_lt (j ^ 2) hr.pos
  have hqk := Nat.mod_lt (k ^ 2) hr.pos
  have hql := Nat.mod_lt (l ^ 2) hr.pos
  have hf : 2 * r * (i + j) + (i ^ 2 % r + j ^ 2 % r) =
      2 * r * (k + l) + (k ^ 2 % r + l ^ 2 % r) := by
    unfold anchorRuler at h
    nlinarith
  have hq : i ^ 2 % r + j ^ 2 % r = k ^ 2 % r + l ^ 2 % r := by
    have he := congrArg (fun n => n % (2 * r)) hf
    simpa only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega : i ^ 2 % r + j ^ 2 % r < 2 * r),
      Nat.mod_eq_of_lt (by omega : k ^ 2 % r + l ^ 2 % r < 2 * r)] using he
  have hs : i + j = k + l := by nlinarith [hr.pos]
  apply quadraticMark_pair hr hodd hi hj hk hl
  unfold quadraticMark
  nlinarith

theorem anchorRuler_step {r h : ℕ} (hr : 0 < r) :
    r < anchorRuler r (h + 1) - anchorRuler r h ∧
      anchorRuler r (h + 1) - anchorRuler r h < 3 * r := by
  have hq := Nat.mod_lt (h ^ 2) hr
  have hq' := Nat.mod_lt ((h + 1) ^ 2) hr
  unfold anchorRuler
  simp only [Nat.mul_add, mul_one]
  constructor <;> omega

theorem anchorRuler_strictMono {r : ℕ} (hr : 0 < r) : StrictMono (anchorRuler r) := by
  apply strictMono_nat_of_lt_succ
  intro h
  have := (anchorRuler_step (h := h) hr).1
  omega

def anchorFactor (a : CoverAlphabet) (p K T r : ℕ) (labels : ℕ → Fin a.size) (h : ℕ) : ℕ :=
  K * anchorRuler r h + anchorOffset a p T (labels h)

def anchor (a : CoverAlphabet) (p K T r : ℕ) (labels : ℕ → Fin a.size) (h : ℕ) : ℕ :=
  p * anchorFactor a p K T r labels h

theorem anchor_eq_baseline (a : CoverAlphabet) (p K T r : ℕ)
    (labels : ℕ → Fin a.size) (h : ℕ) :
    anchor a p K T r labels h = baseline p K T r h +
      p * a.delta (labels h) + a.epsilon (labels h) * (2 * p ^ 2) := by
  unfold anchor anchorFactor anchorOffset baseline baseQuotient
  ring

theorem anchorFactor_pair {a : CoverAlphabet} {K p r : ℕ} (ht : TagWitness a K p)
    (hK : 0 < K) (hr : r.Prime) (hodd : r ≠ 2) (labels : ℕ → Fin a.size)
    {i j k l : ℕ} (hi : i < r) (hj : j < r) (hk : k < r) (hl : l < r)
    (h : anchorFactor a p K ht.shift r labels i + anchorFactor a p K ht.shift r labels j =
      anchorFactor a p K ht.shift r labels k + anchorFactor a p K ht.shift r labels l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hm := congrArg (fun n : ℕ => (n : ZMod K)) h
  simp only [anchorFactor, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    zero_add] at hm
  have ho : anchorOffset a p ht.shift (labels i) + anchorOffset a p ht.shift (labels j) =
      anchorOffset a p ht.shift (labels k) + anchorOffset a p ht.shift (labels l) := by
    rcases ht.pairs _ _ _ _ hm with he | he
    · simp only [he.1, he.2]
    · simp only [he.1, he.2, add_comm]
  have hrul : anchorRuler r i + anchorRuler r j = anchorRuler r k + anchorRuler r l := by
    unfold anchorFactor at h
    nlinarith
  exact anchorRuler_pair hr hodd hi hj hk hl hrul

theorem anchorFactor_sum_ne {a : CoverAlphabet} {K p r : ℕ} (ht : TagWitness a K p)
    (labels : ℕ → Fin a.size) (i j k : ℕ) :
    anchorFactor a p K ht.shift r labels i + anchorFactor a p K ht.shift r labels j ≠
      anchorFactor a p K ht.shift r labels k := by
  intro h
  have hm := congrArg (fun n : ℕ => (n : ZMod K)) h
  simp only [anchorFactor, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    zero_add] at hm
  exact ht.sum_free _ _ _ hm

def anchorSet (a : CoverAlphabet) (p K T r H : ℕ) (labels : ℕ → Fin a.size) : Finset ℕ :=
  (range (H + 1)).image (anchor a p K T r labels)

theorem anchorSet_isSidon {a : CoverAlphabet} {K p r H : ℕ} (ht : TagWitness a K p)
    (hK : 0 < K) (hp : 0 < p) (hr : r.Prime) (hodd : r ≠ 2) (hH : H < r)
    (labels : ℕ → Fin a.size) :
    IsSidon (anchorSet a p K ht.shift r H labels : Set ℕ) := by
  intro x hx y hy z hz w hw h
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
  have hf : anchorFactor a p K ht.shift r labels i + anchorFactor a p K ht.shift r labels k =
      anchorFactor a p K ht.shift r labels j + anchorFactor a p K ht.shift r labels l := by
    unfold anchor at h
    nlinarith
  rcases anchorFactor_pair ht hK hr hodd labels (by have := mem_range.mp hi; omega)
    (by have := mem_range.mp hk; omega) (by have := mem_range.mp hj; omega)
    (by have := mem_range.mp hl; omega) hf with he | he
  · exact Or.inl ⟨congrArg _ he.1, congrArg _ he.2⟩
  · exact Or.inr ⟨congrArg _ he.1, congrArg _ he.2⟩

theorem sidon_union_of_sum_separation {C A : Set ℕ}
    (hC : IsSidon C) (hA : IsSidon A)
    (hCCCA : ∀ c ∈ C, ∀ d ∈ C, ∀ e ∈ C, ∀ a ∈ A, c + d ≠ e + a)
    (hCCAA : ∀ c ∈ C, ∀ d ∈ C, ∀ a ∈ A, ∀ b ∈ A, c + d ≠ a + b)
    (hCA : ∀ c ∈ C, ∀ a ∈ A, ∀ d ∈ C, ∀ b ∈ A,
      c + a = d + b → c = d ∧ a = b)
    (hAACA : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ C, ∀ d ∈ A, a + b ≠ c + d) :
    IsSidon (C ∪ A) := by
  intro x hx y hy z hz w hw h
  rcases hx with hx | hx <;> rcases hz with hz | hz <;>
    rcases hy with hy | hy <;> rcases hw with hw | hw
  · exact hC x hx y hy z hz w hw h
  · exact (hCCCA x hx z hz y hy w hw h).elim
  · exact (hCCCA x hx z hz w hw y hy (by simpa [add_comm] using h)).elim
  · exact (hCCAA x hx z hz y hy w hw h).elim
  · exact (hCCCA y hy w hw x hx z hz h.symm).elim
  · exact Or.inl (hCA x hx z hz y hy w hw h)
  · exact Or.inr (hCA x hx z hz w hw y hy (by simpa [add_comm] using h))
  · exact (hAACA y hy w hw x hx z hz h.symm).elim
  · exact (hCCCA y hy w hw z hz x hx (by simpa [add_comm] using h.symm)).elim
  · have he := hCA z hz x hx y hy w hw (by simpa [add_comm] using h)
    exact Or.inr ⟨he.2, he.1⟩
  · have he := hCA z hz x hx w hw y hy (by simpa [add_comm] using h)
    exact Or.inl ⟨he.2, he.1⟩
  · exact (hAACA y hy w hw z hz x hx (by simpa [add_comm] using h.symm)).elim
  · exact (hCCAA y hy w hw x hx z hz h.symm).elim
  · exact (hAACA x hx z hz y hy w hw h).elim
  · exact (hAACA x hx z hz w hw y hy (by simpa [add_comm] using h)).elim
  · exact hA x hx y hy z hz w hw h

theorem quadraticSeed_lt {p c : ℕ} (hc : c ∈ quadraticSeed p) : c < 2 * p ^ 2 := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
  exact quadraticMark_lt (mem_range.mp ht)

theorem quadraticSeed_mod_inj {p c d : ℕ} (hc : c ∈ quadraticSeed p)
    (hd : d ∈ quadraticSeed p) (he : c % p = d % p) : c = d := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hd
  have ht' := mem_range.mp ht
  have hu' := mem_range.mp hu
  have het : t = u := by
    simpa [quadraticMark, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ht',
      Nat.mod_eq_of_lt hu'] using he
  rw [het]

theorem quadraticSeed_divisible_zero {p c : ℕ} (hc : c ∈ quadraticSeed p)
    (hd : p ∣ c) : c = 0 := by
  have hp : 0 < p := by
    obtain ⟨t, ht, _⟩ := mem_image.mp hc
    have := mem_range.mp ht
    omega
  apply quadraticSeed_mod_inj hc (show 0 ∈ quadraticSeed p by
    exact mem_image.mpr ⟨0, mem_range.mpr hp, by simp [quadraticMark]⟩)
  simp [Nat.mod_eq_zero_of_dvd hd]

theorem anchor_dvd (a : CoverAlphabet) (p K T r : ℕ)
    (labels : ℕ → Fin a.size) (h : ℕ) : p ∣ anchor a p K T r labels h := by
  exact dvd_mul_right _ _

theorem anchor_lower (a : CoverAlphabet) (p K T r : ℕ)
    (labels : ℕ → Fin a.size) (h : ℕ) : 4 * p ^ 2 ≤ anchor a p K T r labels h := by
  unfold anchor anchorFactor anchorOffset
  calc
    4 * p ^ 2 = p * (4 * p) := by ring
    _ ≤ _ := Nat.mul_le_mul_left p (by omega)

theorem anchorSet_dvd {a : CoverAlphabet} {p K T r H c : ℕ}
    {labels : ℕ → Fin a.size} (hc : c ∈ anchorSet a p K T r H labels) : p ∣ c := by
  obtain ⟨h, _, rfl⟩ := mem_image.mp hc
  exact anchor_dvd _ _ _ _ _ _ _

theorem anchorSet_lower {a : CoverAlphabet} {p K T r H c : ℕ}
    {labels : ℕ → Fin a.size} (hc : c ∈ anchorSet a p K T r H labels) :
    4 * p ^ 2 ≤ c := by
  obtain ⟨h, _, rfl⟩ := mem_image.mp hc
  exact anchor_lower _ _ _ _ _ _ _

theorem seed_anchor_union_isSidon {a : CoverAlphabet} {K p r H : ℕ} (ht : TagWitness a K p)
    (hK : 0 < K) (hp : p.Prime) (hpodd : p ≠ 2) (hr : r.Prime) (hrodd : r ≠ 2)
    (hH : H < r) (labels : ℕ → Fin a.size) :
    IsSidon ((quadraticSeed p ∪ anchorSet a p K ht.shift r H labels : Finset ℕ) : Set ℕ) := by
  rw [coe_union]
  apply sidon_union_of_sum_separation (quadraticSeed_isSidon hp hpodd)
    (anchorSet_isSidon ht hK hp.pos hr hrodd hH labels)
  · intro c hc d hd e _ b hb h
    have := quadraticSeed_lt hc
    have := quadraticSeed_lt hd
    have := anchorSet_lower hb
    omega
  · intro c hc d hd b hb e he h
    have := quadraticSeed_lt hc
    have := quadraticSeed_lt hd
    have := anchorSet_lower hb
    omega
  · intro c hc b hb d hd e he h
    have hm := congrArg (fun n => n % p) h
    have hmod : c % p = d % p := by
      simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd (anchorSet_dvd hb),
        Nat.mod_eq_zero_of_dvd (anchorSet_dvd he)] using hm
    have hcd := quadraticSeed_mod_inj hc hd hmod
    exact ⟨hcd, by omega⟩
  · intro b hb e he c hc d hd h
    have hdiv : p ∣ c := by
      have hs := dvd_add (anchorSet_dvd hb) (anchorSet_dvd he)
      rw [h] at hs
      exact (Nat.dvd_add_iff_left (anchorSet_dvd hd)).mpr hs
    have hzero := quadraticSeed_divisible_zero hc hdiv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hb
    obtain ⟨j, _, rfl⟩ := mem_image.mp he
    obtain ⟨k, _, rfl⟩ := mem_image.mp hd
    apply anchorFactor_sum_ne ht labels i j k
    unfold anchor at h
    rw [hzero, zero_add] at h
    nlinarith [hp.pos]

end Bounty.Construction


/- Placing a periodic family of tagged anchors in a finite interval. -/

namespace Bounty.Construction

open Finset Filter Window

theorem bounded_steps {B : ℕ → ℕ} {D : ℕ}
    (hs : ∀ h, B (h + 1) ≤ B h + D) (h j : ℕ) :
    B (h + j) ≤ B h + j * D := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hi := hs (h + j)
    simp only [← Nat.add_assoc, Nat.add_mul, one_mul]
    omega

theorem exists_recent_window {B : ℕ → ℕ} {D R H J x : ℕ}
    (hB : Monotone B) (hstep : ∀ h, B (h + 1) ≤ B h + D)
    (hR : 1 ≤ R) (hRH : R - 1 ≤ H)
    (hlo : B (R - 1) + J ≤ x) (hhi : x < B H + J) :
    ∃ h, h + R ≤ H + 1 ∧ ∀ j : Fin R,
      B (h + j.val) ≤ x ∧ J ≤ x - B (h + j.val) ∧
      x - B (h + j.val) < J + R * D := by
  let P := fun h => B h + J ≤ x
  let t := Nat.findGreatest P H
  have htH : t ≤ H := Nat.findGreatest_le H
  have hRP : P (R - 1) := hlo
  have htR : R - 1 ≤ t := Nat.le_findGreatest hRH hRP
  have htP : P t := Nat.findGreatest_spec hRH hRP
  have htlt : t < H := by
    by_contra! hh
    have he : t = H := by omega
    rw [he] at htP
    exact (not_le_of_gt hhi) htP
  have hnext : x < B (t + 1) + J := by
    have hn := Nat.findGreatest_is_greatest (P := P) (n := H) (k := t + 1)
      (by omega) (by omega)
    dsimp [P] at hn
    omega
  refine ⟨t + 1 - R, by omega, ?_⟩
  intro j
  have hjt : t + 1 - R + j.val ≤ t := by have := j.isLt; omega
  have hjB := hB hjt
  have hgap := bounded_steps hstep (t + 1 - R + j.val) (R - j.val)
  have hsum : t + 1 - R + j.val + (R - j.val) = t + 1 := by
    have := j.isLt
    omega
  rw [hsum] at hgap
  have hmul : (R - j.val) * D ≤ R * D := Nat.mul_le_mul_right D (Nat.sub_le _ _)
  dsimp [P] at htP
  omega

theorem baseline_strictMono {p K r T : ℕ} (hp : 0 < p) (hK : 0 < K) (hr : 0 < r) :
    StrictMono (baseline p K T r) := by
  intro i j hij
  have ha := anchorRuler_strictMono hr hij
  unfold baseline baseQuotient
  exact Nat.mul_lt_mul_of_pos_left
    (Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left ha hK) _) _) hp

theorem baseline_step {p K r T : ℕ} (hr : 0 < r) (h : ℕ) :
    baseline p K T r (h + 1) ≤ baseline p K T r h + 3 * K * p * r := by
  have hs := anchorRuler_step (h := h) hr
  have hlo : anchorRuler r h ≤ anchorRuler r (h + 1) :=
    (anchorRuler_strictMono hr).monotone (Nat.le_succ h)
  have hi : anchorRuler r (h + 1) ≤ anchorRuler r h + 3 * r := by omega
  have hm := Nat.mul_le_mul_left (p * K) hi
  unfold baseline baseQuotient
  nlinarith

def periodicLabels {a : CoverAlphabet} {R : ℕ} (hR : 0 < R)
    (w : Fin R → Fin a.size) (h : ℕ) : Fin a.size := w ⟨h % R, Nat.mod_lt h hR⟩

theorem periodicLabels_rotation {a : CoverAlphabet} {R : ℕ} (hR : 0 < R)
    (w : Fin R → Fin a.size) (h : ℕ) (j : Fin R) :
    periodicLabels hR w (h + j.val) = w (rotation ⟨h % R, Nat.mod_lt h hR⟩ j) := by
  change w ⟨(h + j.val) % R, _⟩ = w (rotation ⟨h % R, _⟩ j)
  apply congrArg w
  apply Fin.ext
  exact (rotation_mod_value hR h j).symm

theorem difference_blocks_insertion {S : Finset ℕ} {x a b c : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hx : x ∉ S)
    (h : (x : ℤ) = a - b + c) : ¬ IsSidon ((S : Set ℕ) ∪ {x}) := by
  intro hs
  have hid : x + b = a + c := by omega
  rcases hs x (Or.inr (Set.mem_singleton _)) a (Or.inl ha)
    b (Or.inl hb) c (Or.inl hc) hid with he | he
  · exact hx (he.1 ▸ ha)
  · exact hx (he.1 ▸ hc)

structure CoverScheme (a : CoverAlphabet) (K : ℕ) where
  period : ℕ
  period_two : 2 ≤ period
  word : Fin period → Fin a.size
  cover : ∀ (p r h T x : ℕ), p.Prime → p ≠ 2 → 0 < r → h < r →
    (∀ j : Fin period, baseline p K T r (h + j.val) ≤ x) →
    (∀ j : Fin period, 2 * p * (a.maxDelta + 2) ≤ x - baseline p K T r (h + j.val)) →
    (∀ j : Fin period, x - baseline p K T r (h + j.val) < 2 * p * (p - 1)) →
    ¬ p ∣ x → ∀ s : Fin period,
    ∃ j, ∃ c ∈ quadraticSeed p, ∃ d ∈ quadraticSeed p,
      (x : ℤ) = c - d + baseline p K T r (h + j.val) +
        (p : ℤ) * a.delta (word (rotation s j)) +
        a.epsilon (word (rotation s j)) * (2 * (p : ℤ) ^ 2)

theorem exists_coverScheme (a : CoverAlphabet) (K : ℕ) : Nonempty (CoverScheme a K) := by
  obtain ⟨R, hR, w, hw⟩ := a.exists_ruler_word K
  exact ⟨⟨R, hR, w, hw⟩⟩

def CoverScheme.labels {a : CoverAlphabet} {K : ℕ} (s : CoverScheme a K) : ℕ → Fin a.size :=
  periodicLabels (by have := s.period_two; omega) s.word

def CoverScheme.seed {a : CoverAlphabet} {K : ℕ} (s : CoverScheme a K) (p T r H : ℕ) : Finset ℕ :=
  quadraticSeed p ∪ anchorSet a p K T r H s.labels

theorem CoverScheme.seed_card {a : CoverAlphabet} {K p T r H : ℕ}
    (s : CoverScheme a K) (hH : H < r) (hrp : r ≤ p) : (s.seed p T r H).card ≤ 2 * p := by
  have hc := card_union_le (quadraticSeed p) (anchorSet a p K T r H s.labels)
  have ha : (anchorSet a p K T r H s.labels).card ≤ H + 1 := by
    exact (card_image_le).trans_eq (card_range _)
  rw [quadraticSeed_card] at hc
  change (quadraticSeed p ∪ anchorSet a p K T r H s.labels).card ≤ 2 * p
  omega

theorem CoverScheme.blocks_interior {a : CoverAlphabet} {K p r H T x : ℕ}
    (s : CoverScheme a K) (hp : p.Prime) (hodd : p ≠ 2) (hK : 0 < K) (hr : 0 < r)
    (hH : H < r) (hRH : s.period - 1 ≤ H)
    (hwidth : 2 * p * (a.maxDelta + 2) + s.period * (3 * K * p * r) ≤ 2 * p * (p - 1))
    (hlo : baseline p K T r (s.period - 1) + 2 * p * (a.maxDelta + 2) ≤ x)
    (hhi : x < baseline p K T r H + 2 * p * (a.maxDelta + 2))
    (hdiv : ¬ p ∣ x) (hx : x ∉ s.seed p T r H) :
    ¬ IsSidon ((s.seed p T r H : Set ℕ) ∪ {x}) := by
  obtain ⟨h, hh, hwindow⟩ := exists_recent_window
    (baseline_strictMono hp.pos hK hr).monotone (baseline_step hr)
    (by have := s.period_two; omega) hRH hlo hhi
  have hhr : h < r := by have := s.period_two; omega
  obtain ⟨j, c, hc, d, hd, hid⟩ := s.cover p r h T x hp hodd hr hhr
    (fun j => (hwindow j).1) (fun j => (hwindow j).2.1)
    (fun j => lt_of_lt_of_le (hwindow j).2.2 hwidth) hdiv
    ⟨h % s.period, Nat.mod_lt _ (by have := s.period_two; omega)⟩
  have hidx : h + j.val < H + 1 := by have := j.isLt; omega
  have ha : anchor a p K T r s.labels (h + j.val) ∈ s.seed p T r H := by
    exact mem_union_right _ (mem_image.mpr ⟨h + j.val, mem_range.mpr hidx, rfl⟩)
  apply difference_blocks_insertion (mem_union_left _ hc) (mem_union_left _ hd) ha hx
  rw [anchor_eq_baseline]
  have hl : s.labels (h + j.val) = s.word (rotation
      ⟨h % s.period, Nat.mod_lt _ (by have := s.period_two; omega)⟩ j) :=
    periodicLabels_rotation _ _ _ _
  rw [hl]
  push_cast
  linear_combination hid

theorem sidon_image_succ {S : Finset ℕ} (hs : IsSidon (S : Set ℕ)) :
    IsSidon (S.image Nat.succ : Set ℕ) := by
  intro x hx y hy z hz w hw he
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
  rcases hs i hi j hj k hk l hl (by omega) with h | h
  · exact Or.inl ⟨congrArg Nat.succ h.1, congrArg Nat.succ h.2⟩
  · exact Or.inr ⟨congrArg Nat.succ h.1, congrArg Nat.succ h.2⟩

theorem sidon_image_pred {S : Finset ℕ} (hs : IsSidon (S : Set ℕ))
    (hpos : ∀ x ∈ S, 1 ≤ x) : IsSidon (S.image Nat.pred : Set ℕ) := by
  intro x hx y hy z hz w hw he
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
  have hi' := hpos i hi
  have hj' := hpos j hj
  have hk' := hpos k hk
  have hl' := hpos l hl
  simp only [Nat.pred_eq_sub_one] at he
  rcases hs i hi j hj k hk l hl (by omega) with h | h
  · exact Or.inl ⟨congrArg Nat.pred h.1, congrArg Nat.pred h.2⟩
  · exact Or.inr ⟨congrArg Nat.pred h.1, congrArg Nat.pred h.2⟩

theorem sidon_shifted_multiples_count {A : Finset ℕ} {N p : ℕ}
    (hp : 1 ≤ p) (hN : N / p ≤ p ^ 2) (hA : IsSidon (A : Set ℕ))
    (hdiv : ∀ x ∈ A, p ∣ x - 1) (hbound : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N) : A.card ≤ 2 * p := by
  let U := A.image Nat.pred
  have hcard : U.card = A.card := by
    apply card_image_iff.mpr
    intro x hx y hy h
    have := (hbound x hx).1
    have := (hbound y hy).1
    simp only [Nat.pred_eq_sub_one] at h
    omega
  rw [← hcard]
  apply sidon_multiples_count hp hN (sidon_image_pred hA (fun x hx => (hbound x hx).1))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact hdiv y hy
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have := (hbound y hy).2
    simp only [Nat.pred_eq_sub_one]
    omega

theorem CoverScheme.exists_truncation {a : CoverAlphabet} {K p T r N : ℕ}
    (s : CoverScheme a K) (hp : 2 ≤ p) (hK : 0 < K) (hr : 0 < r)
    (hT : T < K) (hlarge : 4 * (a.maxDelta + K + 4) ≤ p)
    (hsmall : 6 * K * s.period * r ≤ p) (hRr : s.period ≤ r)
    (hNlo : 10 * p ^ 2 ≤ N) (hNhi : N < baseline p K T r (r - 1)) :
    ∃ H, H < r ∧ s.period - 1 ≤ H ∧
      (∀ z ∈ s.seed p T r H, z < N) ∧
      baseline p K T r (s.period - 1) + 2 * p * (a.maxDelta + 2) ≤ 10 * p ^ 2 ∧
      N - (baseline p K T r H + 2 * p * (a.maxDelta + 2)) ≤ 10 * p ^ 2 ∧
      2 * p * (a.maxDelta + 2) + s.period * (3 * K * p * r) ≤ 2 * p * (p - 1) := by
  let D := 3 * K * p * r
  let J := 2 * p * (a.maxDelta + 2)
  have hR := s.period_two
  have hM : a.maxDelta ≤ p := by omega
  have hKp : K ≤ p := by omega
  have hTbound : p * T ≤ p ^ 2 := by nlinarith
  have hMbound : p * a.maxDelta ≤ p ^ 2 := by nlinarith
  have hunit : 1 ≤ p ^ 2 := by nlinarith
  have hfour : 4 * p ≤ p ^ 2 := by
    have : 4 ≤ p := by omega
    nlinarith
  have hRD2 : 2 * (s.period * D) ≤ p ^ 2 := by
    have hm := Nat.mul_le_mul_left p hsmall
    dsimp [D]
    nlinarith
  have hRD : s.period * D ≤ p ^ 2 := by omega
  have hD : D ≤ p ^ 2 := by
    have hh : D ≤ s.period * D := by nlinarith
    omega
  have hJ2 : 2 * J ≤ p ^ 2 := by dsimp [J]; nlinarith
  have hJ : J ≤ 3 * p ^ 2 := by omega
  have hwidth : J + s.period * D ≤ 2 * p * (p - 1) := by
    have hmid : J + s.period * D ≤ p ^ 2 := by omega
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hB0 : baseline p K T r 0 = 4 * p ^ 2 + p * T := by
    simp only [baseline, baseQuotient, anchorRuler, pow_two, mul_zero, zero_add,
      Nat.zero_mod]
    ring
  have hBR := bounded_steps (baseline_step (p := p) (K := K) (T := T) hr) 0 (s.period - 1)
  simp only [zero_add] at hBR
  rw [hB0] at hBR
  have hRDsub : (s.period - 1) * D ≤ s.period * D :=
    Nat.mul_le_mul_right D (Nat.sub_le _ _)
  have hfirst : baseline p K T r (s.period - 1) + 2 * p ^ 2 + p * a.maxDelta + 1 ≤ N := by
    dsimp [D] at hRDsub hRD
    nlinarith
  have hfirstWidth : baseline p K T r (s.period - 1) + J ≤ 10 * p ^ 2 := by
    dsimp [D] at hRDsub hRD
    nlinarith
  let P := fun h => baseline p K T r h + 2 * p ^ 2 + p * a.maxDelta + 1 ≤ N
  let H := Nat.findGreatest P (r - 1)
  have hHle : H ≤ r - 1 := Nat.findGreatest_le _
  have hHP : P H := Nat.findGreatest_spec (by omega : s.period - 1 ≤ r - 1) hfirst
  have hHR : s.period - 1 ≤ H := Nat.le_findGreatest (by omega : s.period - 1 ≤ r - 1) hfirst
  have hHlt : H < r - 1 := by
    by_contra! hh
    have he : H = r - 1 := by omega
    rw [he] at hHP
    dsimp [P] at hHP
    omega
  have hnext : N < baseline p K T r (H + 1) + 2 * p ^ 2 + p * a.maxDelta + 1 := by
    have hh := Nat.findGreatest_is_greatest (P := P) (n := r - 1) (k := H + 1)
      (by omega) (by omega)
    dsimp [P] at hh
    omega
  have hstep := baseline_step (p := p) (K := K) (T := T) hr H
  have htail : N - (baseline p K T r H + J) ≤ 10 * p ^ 2 := by
    dsimp [D] at hD
    omega
  refine ⟨H, by omega, hHR, ?_, hfirstWidth, htail, hwidth⟩
  intro z hz
  rcases mem_union.mp hz with hz | hz
  · have hzlt := quadraticSeed_lt hz
    omega
  · obtain ⟨h, hh, rfl⟩ := mem_image.mp hz
    have hhH : h ≤ H := by have := mem_range.mp hh; omega
    have hb := (baseline_strictMono (T := T) (by omega : 0 < p) hK hr).monotone hhH
    rw [anchor_eq_baseline]
    have hδ := a.delta_le (s.labels h)
    have hε := a.epsilon_le (s.labels h)
    have hd := Nat.mul_le_mul_left p hδ
    have he := Nat.mul_le_mul_right (2 * p ^ 2) hε
    simp only [one_mul] at he
    dsimp [P] at hHP
    omega

theorem blocked_succ {S : Finset ℕ} {x : ℕ}
    (hblock : ¬ IsSidon ((S : Set ℕ) ∪ {x})) :
    ¬ IsSidon ((S.image Nat.succ : Set ℕ) ∪ {x + 1}) := by
  intro hs
  apply hblock
  have hmem (z : ℕ) (hz : z ∈ (S : Set ℕ) ∪ {x}) :
      z.succ ∈ (S.image Nat.succ : Set ℕ) ∪ {x + 1} := by
    rcases hz with hz | hz
    · exact Or.inl (mem_image.mpr ⟨z, hz, rfl⟩)
    · have he := Set.mem_singleton_iff.mp hz
      exact Or.inr (by simpa only [he] using Set.mem_singleton (x + 1))
  intro a ha b hb c hc d hd h
  rcases hs a.succ (hmem a ha) b.succ (hmem b hb) c.succ (hmem c hc) d.succ (hmem d hd)
    (by omega) with he | he
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

theorem maximal_completion_shifted {N p low high : ℕ} {S : Finset ℕ}
    (hp : 1 ≤ p) (hN : N / p ≤ p ^ 2)
    (hlow : low ≤ 10 * p ^ 2) (hhigh : N - high ≤ 10 * p ^ 2)
    (hS : ∀ x ∈ S, x < N) (hs : IsSidon (S : Set ℕ)) (hcard : S.card ≤ 2 * p)
    (hblocked : ∀ x < N, x ∉ S → low ≤ x → x < high → ¬ p ∣ x →
      ¬ IsSidon ((S : Set ℕ) ∪ {x})) :
    ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧ A.card ≤ 14 * p := by
  classical
  let S' := S.image Nat.succ
  let E₁ := Icc 1 (1 + low)
  let E₂ := Icc (high + 1) (high + 1 + (N - high))
  let E₃ := (Icc 1 N).filter fun x => p ∣ x - 1
  have hS' : S' ⊆ Icc 1 N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have := hS y hy
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hb : ∀ x ∈ Icc 1 N, x ∉ S' → x ∉ E₁ → x ∉ E₂ → x ∉ E₃ →
      ¬ IsSidon ((S' : Set ℕ) ∪ {x}) := by
    intro x hx hxS hx₁ hx₂ hx₃
    have hxlo := (mem_Icc.mp hx).1
    have hxhi := (mem_Icc.mp hx).2
    have hsx : x - 1 ∉ S := by
      intro hh
      apply hxS
      exact mem_image.mpr ⟨x - 1, hh, by omega⟩
    have hlo : low ≤ x - 1 := by
      have hh : ¬ (1 ≤ x ∧ x ≤ 1 + low) := by simpa only [E₁, mem_Icc] using hx₁
      omega
    have hhi : x - 1 < high := by
      have hh : ¬ (high + 1 ≤ x ∧ x ≤ high + 1 + (N - high)) := by
        simpa only [E₂, mem_Icc] using hx₂
      omega
    have hdiv : ¬ p ∣ x - 1 := by
      intro hh
      exact hx₃ (mem_filter.mpr ⟨hx, hh⟩)
    have hh := blocked_succ (hblocked (x - 1) (by omega) hsx hlo hhi hdiv)
    simpa only [Nat.sub_add_cancel hxlo] using hh
  have h₁ : ∀ T : Finset ℕ, T ⊆ E₁ → IsSidon (T : Set ℕ) → T.card ≤ 5 * p := by
    intro T hT ht
    exact sidon_interval_count_five_mul hp hlow ht (fun x hx => mem_Icc.mp (hT hx))
  have h₂ : ∀ T : Finset ℕ, T ⊆ E₂ → IsSidon (T : Set ℕ) → T.card ≤ 5 * p := by
    intro T hT ht
    exact sidon_interval_count_five_mul hp hhigh ht (fun x hx => mem_Icc.mp (hT hx))
  have h₃ : ∀ T : Finset ℕ, T ⊆ E₃ → IsSidon (T : Set ℕ) → T.card ≤ 2 * p := by
    intro T hT ht
    apply sidon_shifted_multiples_count hp hN ht
    · intro x hx
      exact (mem_filter.mp (hT hx)).2
    · intro x hx
      exact mem_Icc.mp (mem_filter.mp (hT hx)).1
  obtain ⟨A, _, hA, hbound⟩ := exists_maximal_completion_with_exception_bounds hS'
    (sidon_image_succ hs) hb h₁ h₂ h₃
  have hc : S'.card ≤ S.card := card_image_le
  exact ⟨A, hA, by omega⟩

theorem CoverScheme.small_maximal_of_primes {a : CoverAlphabet} {K p r N : ℕ}
    (s : CoverScheme a K) (ht : TagWitness a K p) (hK : 0 < K)
    (hp : p.Prime) (hpodd : p ≠ 2) (hr : r.Prime) (hrodd : r ≠ 2)
    (hlarge : 4 * (a.maxDelta + K + 4) ≤ p) (hsmall : 6 * K * s.period * r ≤ p)
    (hRr : s.period ≤ r) (hrp : r ≤ p) (hNlo : 10 * p ^ 2 ≤ N)
    (hNhi : N < baseline p K ht.shift r (r - 1)) (hN : N / p ≤ p ^ 2) :
    ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧ A.card ≤ 14 * p := by
  obtain ⟨H, hHr, hHR, hhost, hlo, hhi, hwidth⟩ := s.exists_truncation hp.two_le hK hr.pos
    ht.shift_lt hlarge hsmall hRr hNlo hNhi
  apply maximal_completion_shifted (by have := hp.two_le; omega) hN hlo hhi hhost
    (seed_anchor_union_isSidon ht hK hp hpodd hr hrodd hHr s.labels)
    (s.seed_card hHr hrp)
  intro x _ hx hxl hxh hxdiv
  exact s.blocks_interior hp hpodd hK hr.pos hHr hHR hwidth hxl hxh hxdiv hx

end Bounty.Construction


/- Prime selection and the final asymptotic bound. -/

namespace Bounty.Construction

open Finset Filter Window

theorem exists_cube_scale {N n₀ : ℕ} (hN : n₀ ^ 3 ≤ N) :
    ∃ n, n₀ ≤ n ∧ n ^ 3 ≤ N ∧ N < (n + 1) ^ 3 := by
  let P := fun n : ℕ => n ^ 3 ≤ N
  have hbase : n₀ ≤ N + 1 := by
    have hh : n₀ ≤ n₀ ^ 3 := Nat.le_self_pow (by decide) n₀
    omega
  let n := Nat.findGreatest P (N + 1)
  have hspec : P n := Nat.findGreatest_spec hbase hN
  have hlo : n₀ ≤ n := Nat.le_findGreatest hbase hN
  have hle : n ≤ N + 1 := Nat.findGreatest_le _
  have hlt : n < N + 1 := by
    by_contra! h
    have he : n = N + 1 := by omega
    rw [he] at hspec
    dsimp [P] at hspec
    have hh : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by decide) (N + 1)
    omega
  refine ⟨n, hlo, hspec, ?_⟩
  have hn := Nat.findGreatest_is_greatest (P := P) (n := N + 1) (k := n + 1)
    (by omega) (by omega)
  dsimp [P] at hn
  omega

theorem cube_scale_real_bound {N n : ℕ} (hn : n ^ 3 ≤ N) :
    (n : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hc : (n : ℝ) ^ (3 : ℕ) ≤ N := by exact_mod_cast hn
  have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (3 : ℕ)) hc
    (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
  have hroot : ((n : ℝ) ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹) = n := by
    simpa only [Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (Nat.cast_nonneg n) (by decide : (3 : ℕ) ≠ 0)
  rw [hroot] at hh
  simpa only [one_div] using hh

theorem anchorRuler_last_lower {r : ℕ} (hr : 2 ≤ r) : r ^ 2 ≤ anchorRuler r (r - 1) := by
  have hprod : r * r ≤ 2 * r * (r - 1) := by
    calc
      r * r ≤ r * (2 * (r - 1)) := Nat.mul_le_mul_left r (by omega)
      _ = 2 * r * (r - 1) := by ring
  unfold anchorRuler
  simpa only [pow_two] using hprod.trans (Nat.le_add_right _ _)

theorem baseline_last_large {p r K T n N : ℕ} (hn : 1 ≤ n) (hr : 2 ≤ r)
    (hK : 1 ≤ K) (hp : 8 * n ≤ p) (hnr : n ≤ r) (hN : N < (n + 1) ^ 3) :
    N < baseline p K T r (r - 1) := by
  have hn1 : n + 1 ≤ 2 * n := by omega
  have h8 : (n + 1) ^ 3 ≤ 8 * n ^ 3 := by
    have hh := Nat.pow_le_pow_left hn1 3
    nlinarith
  have hr2 : n ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hnr 2
  have hp1 : 8 * n ^ 3 ≤ p * r ^ 2 := by
    have hh := Nat.mul_le_mul hp hr2
    nlinarith
  have ha := anchorRuler_last_lower hr
  have hka : r ^ 2 ≤ K * anchorRuler r (r - 1) := by
    have hh : anchorRuler r (r - 1) ≤ K * anchorRuler r (r - 1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (anchorRuler r (r - 1)) hK
    omega
  have hh := Nat.mul_le_mul_left p hka
  unfold baseline baseQuotient
  nlinarith

theorem choose_primes_at_scale {D n N : ℕ} (hD : 16 ≤ D) (hn : 2 ≤ n)
    (hbig : 40 * D ^ 2 ≤ n) (hNlo : n ^ 3 ≤ N) (hNhi : N < (n + 1) ^ 3) :
    ∃ p r, p.Prime ∧ r.Prime ∧ p ≠ 2 ∧ r ≠ 2 ∧
      D * n < p ∧ p ≤ 2 * D * n ∧ n < r ∧ r ≤ 2 * n ∧
      r ≤ p ∧ 10 * p ^ 2 ≤ N ∧ N / p ≤ p ^ 2 := by
  obtain ⟨p, hp, hpl, hpu⟩ := Nat.exists_prime_lt_and_le_two_mul (D * n) (by positivity)
  obtain ⟨r, hr, hrl, hru⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hpu' : p ≤ 2 * D * n := by nlinarith
  have hp2 : p ^ 2 ≤ 4 * D ^ 2 * n ^ 2 := by
    have hh := Nat.pow_le_pow_left hpu' 2
    nlinarith
  have hbig' : 40 * D ^ 2 * n ^ 2 ≤ n ^ 3 := by
    have hh := Nat.mul_le_mul_right (n ^ 2) hbig
    nlinarith
  have hten : 10 * p ^ 2 ≤ N := by nlinarith
  have hnr : r ≤ p := by nlinarith
  have hpodd : p ≠ 2 := by nlinarith
  have hrodd : r ≠ 2 := by omega
  have hNcube : N ≤ p ^ 3 := by
    have hsmall : n + 1 ≤ p := by nlinarith
    have hh := Nat.pow_le_pow_left hsmall 3
    omega
  have hdiv : N / p ≤ p ^ 2 := by
    have hh := Nat.div_mul_le_self N p
    nlinarith [hp.pos]
  exact ⟨p, r, hp, hr, hpodd, hrodd, hpl, hpu', hrl, hru, hnr, hten, hdiv⟩

theorem CoverScheme.small_maximal_at_scale {a : CoverAlphabet} {K D n p r N : ℕ}
    (s : CoverScheme a K) (ht : TagWitness a K p) (hK : 0 < K)
    (hp : p.Prime) (hpodd : p ≠ 2) (hr : r.Prime) (hrodd : r ≠ 2)
    (hD : 16 ≤ D) (hDn : 12 * K * s.period ≤ D)
    (hn : 2 ≤ n) (hnM : 4 * (a.maxDelta + K + 4) ≤ n) (hnR : s.period ≤ n)
    (hpl : D * n < p) (hrl : n < r) (hru : r ≤ 2 * n) (hrp : r ≤ p)
    (hNlo : 10 * p ^ 2 ≤ N) (hNhi : N < (n + 1) ^ 3) (hNdiv : N / p ≤ p ^ 2) :
    ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧ A.card ≤ 14 * p := by
  have hnp : n ≤ p := by nlinarith
  have hsmall : 6 * K * s.period * r ≤ p := by
    calc
      6 * K * s.period * r ≤ 6 * K * s.period * (2 * n) :=
        Nat.mul_le_mul_left _ hru
      _ = (12 * K * s.period) * n := by ring
      _ ≤ D * n := Nat.mul_le_mul_right n hDn
      _ ≤ p := Nat.le_of_lt hpl
  have hlast : N < baseline p K ht.shift r (r - 1) :=
    baseline_last_large (by omega) (by omega) (by omega) (by nlinarith) (by omega) hNhi
  exact s.small_maximal_of_primes ht hK hp hpodd hr hrodd (by omega) hsmall
    (by omega) hrp hNlo hlast hNdiv

theorem eventual_small_maximal_sets :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ,
      Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧
      (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨a, b, K, hK, htags⟩ := exists_two_tagged_alphabets
  obtain ⟨sa⟩ := exists_coverScheme a K
  obtain ⟨sb⟩ := exists_coverScheme b K
  let R := sa.period + sb.period
  let M := a.maxDelta + b.maxDelta
  let D := 12 * K * R + 16
  let n₀ := 40 * D ^ 2 + 4 * (M + K + 4) + R + 2
  have hD : 16 ≤ D := by dsimp [D]; omega
  refine ⟨(28 : ℝ) * D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (n₀ ^ 3)] with N hN
  obtain ⟨n, hn₀, hnlo, hnhi⟩ := exists_cube_scale hN
  have hn : 2 ≤ n := by dsimp [n₀] at hn₀; omega
  have hbig : 40 * D ^ 2 ≤ n := by dsimp [n₀] at hn₀; omega
  obtain ⟨p, r, hp, hr, hpodd, hrodd, hpl, hpu, hrl, hru, hrp, hNlo, hNdiv⟩ :=
    choose_primes_at_scale hD hn hbig hnlo hnhi
  have hdone (c : CoverAlphabet) (s : CoverScheme c K) (ht : TagWitness c K p)
      (hcM : c.maxDelta ≤ M) (hcR : s.period ≤ R) :
      ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧ A.card ≤ 14 * p := by
    have hDn : 12 * K * s.period ≤ D := by
      have hh := Nat.mul_le_mul_left (12 * K) hcR
      dsimp [D]
      omega
    have hnM : 4 * (c.maxDelta + K + 4) ≤ n := by dsimp [n₀] at hn₀; omega
    have hnR : s.period ≤ n := by dsimp [n₀] at hn₀; omega
    exact s.small_maximal_at_scale ht hK hp hpodd hr hrodd hD hDn hn hnM hnR
      hpl hrl hru hrp hNlo hnhi hNdiv
  have hA : ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧ A.card ≤ 14 * p := by
    rcases htags p with ha | hb
    · obtain ⟨ht⟩ := ha
      exact hdone a sa ht (by dsimp [M]; omega) (by dsimp [R]; omega)
    · obtain ⟨ht⟩ := hb
      exact hdone b sb ht (by dsimp [M]; omega) (by dsimp [R]; omega)
  obtain ⟨A, hA, hcard⟩ := hA
  refine ⟨A, hA, ?_⟩
  have hnat : A.card ≤ 28 * D * n := by nlinarith
  have hreal : (A.card : ℝ) ≤ (28 : ℝ) * D * n := by exact_mod_cast hnat
  have hroot := cube_scale_real_bound hnlo
  exact hreal.trans (mul_le_mul_of_nonneg_left hroot (by positivity))

end Bounty.Construction

namespace Bounty

theorem target : fcTypeOfName% "Erdos156.erdos_156" :=
  target_iff_small_maximal_sets.mpr Construction.eventual_small_maximal_sets

end Bounty
