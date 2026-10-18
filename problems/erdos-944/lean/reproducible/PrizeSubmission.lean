/-
Copyright 2026 Liam Kruer and Jensen Kohlmeyer.

Supplementary submission wrapper. The imported proof remains byte-for-byte
identical to the recorded complete-math-solutions source. This wrapper makes
finiteness explicit and states the positive answer without answer syntax.
OpenAI Codex assisted with preparation of this wrapper and verification.
-/
import Solutions.Erdos944

namespace Erdos944Prize
open Bounty.Erdos944Proof

universe u

/-- Transfer a finite witness into an arbitrary universe, retaining finiteness. -/
theorem finite_universe_lift {V : Type} [Finite V] [Nonempty V]
    (G : SimpleGraph V) {k r : Nat} (hk : 0 < k)
    (hG : Erdos944.SimpleGraph.IsErdos944 G (k + 1) r) :
    ∃ (W : Type u) (H : SimpleGraph W), Finite W ∧
      Erdos944.SimpleGraph.IsErdos944 H (k + 1) r := by
  exact ⟨ULift.{u} V, G.comap ULift.down, inferInstance,
    erdos944_of_equiv G (Equiv.ulift : ULift.{u} V ≃ V) hk hG⟩

theorem finite_erdos944_four_from_arithmetic_conditions {n r t : Nat} [NeZero n]
    (hrt : r ≤ t) (hn : n % 3 = 1) (hq : 3 * t + 1 ∣ n) (htn : 3 * t + 1 < n)
    (a : ZMod (3 * t + 1) → (ZMod n)ˣ) (ha : ShortCompatible (3 * t + 1) a)
    (hwords : ∀ s ∈ canonicalConnections a, ∀ F : Finset (ZMod n), F.card ≤ 6 * r + 2 →
      ∃ w : Fin 3 → ZMod n, w 0 + w 1 + w 2 = s ∧
        (∀ p, w p ∈ canonicalConnections a ∨ -w p ∈ canonicalConnections a) ∧
        (∀ p, w p ∉ F))
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections a, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit n (K * ((a i : ZMod n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  have hrobust : ∀ s ∈ canonicalConnections a, HasSignedWords (canonicalConnections a) r s :=
    fun s hs => hasSignedWords_of_avoidance (canonicalConnections a) r s (hwords s hs)
  obtain ⟨G, hG⟩ := erdos944_four_of_short_compatible hrt hn hq htn a ha hrobust hcharacter
  exact finite_universe_lift G (by omega : 0 < 3) hG

theorem finite_erdos944_four_of_integer_data {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (hwords : ∀ s ∈ canonicalConnections p.unitDirection, ∀ F : Finset (ZMod p.n), F.card ≤ 6 * r + 2 →
      ∃ w : Fin 3 → ZMod p.n, w 0 + w 1 + w 2 = s ∧
        (∀ j, w j ∈ canonicalConnections p.unitDirection ∨ -w j ∈ canonicalConnections p.unitDirection) ∧
        (∀ j, w j ∉ F))
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections p.unitDirection, characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G 4 r :=
  finite_erdos944_four_from_arithmetic_conditions p.gap_lower p.order_three p.gap_divides
    (cyclic_data_gap_lt_order p) p.unitDirection (cyclic_data_shortCompatible p) hwords hcharacter

theorem finite_erdos944_four_of_character_condition {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections p.unitDirection, characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G 4 r :=
  finite_erdos944_four_of_integer_data p
    (fun _ hs F hF => cyclic_data_word_avoidance p hs F hF) hcharacter

theorem finite_erdos944_four_of_periodic_rigidity {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (hrigidity : ∀ K P b : Int, K * p.family.period = P * p.n + b →
      2 * |b| < (p.family.period : Int) → p.family.MiddleThirdCharacter P b →
      ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  apply finite_erdos944_four_of_character_condition p
  intro K hK
  obtain ⟨P, b, he, hb, hphases⟩ := cyclic_data_rounded_character p K hK
  exact hrigidity K P b he hb hphases

theorem finite_erdos944_four (r : Nat) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  obtain ⟨p⟩ := exists_cyclic_integer_data r
  let : NeZero p.n := ⟨Nat.ne_of_gt (cyclic_data_order_pos p)⟩
  apply finite_erdos944_four_of_periodic_rigidity p
  intro K P b hidentity hb hchar
  exact cyclic_data_periodic_rigidity p hidentity hb hchar

theorem finite_erdos944_ge_six {k : Nat} (hk : 6 ≤ k) (r : Nat) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G k r := by
  have hsucc : k - 1 + 1 = k := by omega
  have hG := higher_ge_six_erdos944 (r := r) hk
  have h := finite_universe_lift (k := k - 1) (higherGraph k (18 * r + 3) (24 * r + 12))
    (by omega) (by simpa only [hsucc] using hG)
  simpa only [hsucc] using h

theorem finite_erdos944_five (r : Nat) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G 5 r := by
  exact finite_universe_lift (k := 4) (higherGraph 5 (18 * r + 20) (24 * r + 12))
    (by omega) (higher_five_erdos944 r)

/-- Finite witnesses for every number of colors k ≥ 4 and every natural robustness r. -/
theorem finite_all {k : Nat} (hk : 4 ≤ k) (r : Nat) :
    ∃ (V : Type u) (G : SimpleGraph V), Finite V ∧ Erdos944.SimpleGraph.IsErdos944 G k r := by
  by_cases hfour : k = 4
  · subst k
    exact finite_erdos944_four r
  by_cases hfive : k = 5
  · subst k
    exact finite_erdos944_five r
  exact finite_erdos944_ge_six (by omega) r

/-- The literal mathematical assertion, without an answer placeholder. -/
theorem target : ∀ k ≥ 4, ∀ r ≥ 1,
    ∃ (V : Type u) (G : SimpleGraph V),
      Finite V ∧ G.IsCritical k ∧
        ∀ edges : Set (Sym2 V), G.IsCriticalEdges edges → r < edges.ncard := by
  intro k hk r _hr
  obtain ⟨V, G, hfinite, hG⟩ := finite_all hk r
  exact ⟨V, G, hfinite, hG⟩

/-- Explicit version of the original positive answer to the imported benchmark. -/
theorem benchmark_target : True ↔ ∀ k ≥ 4, ∀ r ≥ 1,
    ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G k r := by
  constructor
  · intro _ k hk r hr
    obtain ⟨V, G, _hfinite, hG⟩ := target k hk r hr
    exact ⟨V, G, hG⟩
  · intro _
    trivial

/-- The explicit positive answer has exactly the benchmark's elaborated type. -/
theorem benchmark_type_check : fcTypeOfName% "Erdos944.erdos_944" :=
  benchmark_target

end Erdos944Prize

#print axioms Bounty.target
#print axioms Erdos944Prize.finite_all
#print axioms Erdos944Prize.target
#print axioms Erdos944Prize.benchmark_target
#print axioms Erdos944Prize.benchmark_type_check
#check Erdos944Prize.target
