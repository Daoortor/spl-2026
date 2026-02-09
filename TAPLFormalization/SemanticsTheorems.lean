import TAPLFormalization.Semantics

lemma no_step_from_NV : IsNumericValue t → ∀ t', ¬(t ~> t') := by
  intro t_nv t'
  induction t_nv generalizing t' with
  | zero => intro; contradiction
  | succ t'_nv ih =>
    intro st
    cases st
    apply ih <;> assumption

theorem smallStep_deterministic : (t₁ ~> t₂) → (t₁ ~> t₃) → (t₂ = t₃) := by
  intro st₂ st₃
  induction t₁ generalizing t₂ t₃ <;> cases st₂ <;> cases st₃
  any_goals rfl
  any_goals contradiction
  -- When st₂ and st₃ are from the same constructor, we can apply (one of) ih
  any_goals (congr; apply_assumption <;> assumption)
  -- Otherwise, we have a step t~>t', where t is an NV -- contradiction
  all_goals grind [no_step_from_NV, IsNumericValue]

def isNF (t : Term) := ∀ (t' : Term), ¬(t ~> t')

theorem isNF_if_isValue : ∀ (t : Term),  IsValue t → isNF t := by
  intro t t_value t' bad_step
  cases t_value <;> try contradiction
  rename_i t_nv
  exact no_step_from_NV t_nv t' bad_step

theorem boolean_isNF_iff_isValue : ∀ (t : Term), BooleanTerm t → (isNF t ↔ IsValue t) := by
  intro t t_boolean
  apply Iff.intro
  · intro t_nf
    cases t_boolean <;> try constructor
    rename_i t₁ t₂ t₃ t₁_boolean t₂_boolean t₃_boolean
    suffices h : False by contradiction
    induction t₁_boolean generalizing t₂ t₃
    · exact t_nf t₂ .IfTrue
    · exact t_nf t₃ .IfFalse
    · rename_i t₁₁ t₁₂ t₁₃ t₁₁_boolean t₁₂_boolean t₁₃_boolean ih₁ ih₂ ih₃
      let t₁_not_NF := Not.intro $ ih₁ t₁₂_boolean t₁₃_boolean
      rw [isNF, Classical.not_forall_not] at t₁_not_NF
      let ⟨t', st⟩ := t₁_not_NF
      exact t_nf _ (.If st)
  · exact isNF_if_isValue t

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
  intro t
  by_cases h : isNF t
  case pos =>
    exists t
    constructor
    · trivial
    · constructor
  case neg =>
    rw [isNF, Classical.not_forall_not] at h
    let ⟨t', st⟩ := h
    let ⟨t₀, ⟨t₀_nf, t'_t₀⟩⟩ := termination t'
    exists t₀
    constructor
    · trivial
    · constructor <;> assumption
decreasing_by
  rename_i a
  clear a
  induction st <;> grind [isNF]

lemma smallSteps_in_context (f : Term → Term) : (∀ {t t'}, t ~> t' → (f t) ~> (f t'))
  → t ~>* t' → (f t) ~>* (f t') := by
  intro h_st t_sts_t'
  induction t_sts_t' with
  | refl => constructor
  | tail st sts ih =>
    rename_i t₁ t₂ t₃
    exact SmallSteps.tail (h_st st) ih
