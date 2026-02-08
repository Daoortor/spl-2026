import TAPLFormalization.Semantics

theorem smallStepDeterministic : (t₁ ~> t₂) → (t₁ ~> t₃) → (t₂ = t₃) := by
  sorry

def isNF (t : Term) := ∀ (t' : Term), ¬(t ~> t')

inductive isValue : Term → Prop where
  | value v : isValue (.value v)

theorem isNF_iff_isValue : ∀ (t : Term), isNF t ↔ isValue t := by
  sorry

theorem NF_unique (tu : t ~>* u) (tu' : t ~>* u') (nfu : isNF u) (nfu' : isNF u') : u = u' := by
  induction tu with
  | refl =>
    induction tu' with
    | refl => rfl
    | tail b hb ih =>
      rename_i aa bb cc dd
      cases nfu cc b
  | tail b hb ih  =>
    induction tu' with
    | refl =>
      rename_i aa bb cc dd
      cases nfu' bb b
    | tail b hb ih =>
      rename_i aa bb cc dd ee ff gg hh tt
      let hh := smallStepDeterministic hh b
      rw[hh] at hb
      let ih := ih hb nfu
      exact ih

theorem termination : ∀ (t : Term), ∃ t', isNF t' ∧ t ~>* t' := by
  sorry
