import TAPLFormalization.Semantics

theorem smallStepDeterministic : (t₁ ~> t₂) → (t₁ ~> t₃) → (t₂ = t₃) := by
  sorry

def isNF (t : Term) := ∀ (t' : Term), ¬(t ~> t')

inductive isValue : Term → Prop where
  | value v : isValue (.value v)

theorem isNF_iff_isValue : ∀ (t : Term), isNF t ↔ isValue t := by
  sorry

theorem NF_unique : (t ~>* u) → (t ~>* u') → isNF u → isNF u' → u = u' := by
  sorry

theorem termination : ∀ (t : Term), ∃ t', isNF t' ∧ t ~>* t' := by
  sorry
