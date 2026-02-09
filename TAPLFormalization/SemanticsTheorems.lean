import TAPLFormalization.Semantics

lemma no_step_from_NV : NumericValue t → ∀ t', ¬(t ~> t') := by
  intro t_nv t'
  induction t_nv generalizing t' with
  | zero => intro; contradiction
  | succ t'_nv ih =>
    intro st
    cases st
    apply ih <;> assumption

theorem smallStep_deterministic : (t₁ ~> t₂) → (t₁ ~> t₃) → (t₂ = t₃) := by
  intro st₂ st₃
  induction t₁ generalizing t₂ t₃ <;> try contradiction
  all_goals cases st₂ <;> cases st₃
  any_goals rfl
  any_goals contradiction
  -- When st₂ and st₃ are from the same constructor, we can apply (one of) ih
  any_goals try (congr; apply_assumption <;> assumption)
  -- Otherwise, we have a step from NV
  all_goals grind [no_step_from_NV, NumericValue.succ]

def isNF (t : Term) := ∀ (t' : Term), ¬(t ~> t')

theorem boolean_isNF_iff_isValue : ∀ (t : Term), BooleanTerm t → (isNF t ↔ Value t) := by
  sorry

theorem isNF_if_isValue : ∀ (t : Term),  Value t → isNF t := by
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
      let hh := smallStep_deterministic hh b
      rw[hh] at hb
      let ih := ih hb nfu
      exact ih

theorem termination : ∀ (t : Term), ∃ t', isNF t' ∧ t ~>* t' := by
  sorry
