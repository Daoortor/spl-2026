import TAPLFormalization.«02-lambda».Semantics

lemma CV.smallStep_deterministic : SmallStep t₁ t₂ ↔ .some t₂ = next t₁ := by
  constructor
  · intro st
    induction st with
    | appAbs subst_eq =>
      rename_i s t₂ t₁
      rw [next, subst_eq]
    | appBody st ih =>
      rename_i t₁ t₁' t₂
      rw [next, ← ih, Option.map_apply, Option.map_some]
      · intro _ _ t₁_eq
        rw [t₁_eq] at st
        cases st
      · intro _ t₁_eq
        rw [t₁_eq] at st
        cases st
    | appArg st ih =>
      rename_i t₂ t₂' t₁
      rw [next, ← ih, Option.map_apply, Option.map_some]
      intro _ t₁_eq
      rw [t₁_eq] at st
      cases st
  · intro next_eq
    induction t₁ generalizing t₂ <;> try simp [next] at next_eq
    rename_i body arg body_ih arg_ih
    cases body <;> try simp [next] at next_eq
    · rename_i body₂ arg₂
      cases h : (next (body₂.app arg₂)) <;> (rw [h, Option.map] at next_eq; cases next_eq)
      apply SmallStep.appBody
      exact body_ih (Eq.symm h)
    · rename_i body₂
      cases arg
      · simp [next, Option.map_apply, Option.map] at next_eq
      · simp [next, Option.map_apply, Option.map] at next_eq
      · rename_i body₃ arg₃
        cases h : (next (body₃.app arg₃))
          <;> rw [next, h, Option.map_apply, Option.map] at next_eq
          <;> try (intros; contradiction)
        injection next_eq with next_eq
        rw [next_eq]
        let st' := arg_ih (Eq.symm h)
        apply SmallStep.appArg st'
      · rw [next] at next_eq
        injection next_eq
        apply SmallStep.appAbs
        assumption
