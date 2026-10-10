import PaperMain

def Intended196 : Prop := ∃ p : ℕ ≃ ℕ, ∀ a b c d : ℕ,
  a < b → b < c → c < d →
  ¬ (p a + p c = 2 * p b ∧ p b + p d = 2 * p c)
theorem checked196 : Intended196 := Bounty.paper_main
#check @checked196
#print checked196
#print axioms checked196
#print HasMonotoneAP
