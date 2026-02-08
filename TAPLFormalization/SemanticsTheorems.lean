import TAPLFormalization.Semantics

theorem headSmallStep_deterministic : HeadSmallStep t t₁ → HeadSmallStep t t₂ → (t₁ = t₂) := by
  intro h_st₁ h_st₂
  cases h_st₁ <;> cases h_st₂ <;> rfl

inductive isRedex : Term → Prop
  | ifTrue : isRedex (.ifThenElse (.value .trueV) t₂ t₃)
  | ifFalse : isRedex (.ifThenElse (.value .falseV) t₂ t₃)
  | predZero : isRedex (.pred (.value (.nv .zero)))
  | predSucc : isRedex (.pred (.succ (.value (.nv n))))
  | isZeroZero : isRedex (.isZero (.value (.nv .zero)))
  | isZeroSucc : isRedex (.isZero (.value (.nv (.succ n))))

lemma isRedex_iff_can_headSmallStep : (∃ t', HeadSmallStep t t') ↔ isRedex t := by
  apply Iff.intro
  · rintro ⟨t', h_st⟩
    cases h_st <;> constructor
  · intro t_redex
    cases t_redex <;> exact ⟨_, by constructor⟩

def isDecomposition (t : Term) (ctx : Ctx) (t' : Term) := isRedex t' ∧ t = ctx.fill t'

lemma decomposition_unique_with_hole (t : Term) : isDecomposition t ctx t₁ → isRedex t → ctx = .hole ∧ t₁ = t := by
  rintro ⟨t₁_redex, t_eq₁⟩ t_redex
  cases t_redex <;> cases ctx <;> simp [Ctx.fill] at t_eq₁ <;> try (
    constructor
    · rfl
    · try exact t_eq₁
      try exact Eq.symm t_eq₁
  )
  all_goals rename Ctx => ctx'
  all_goals try let ⟨t_eq₁, _, _⟩ := t_eq₁
  all_goals cases ctx' <;> simp [Ctx.fill] at t_eq₁
  all_goals try (
    rw [← t_eq₁] at t₁_redex
    cases t₁_redex
  )
  rename_i ctx''
  cases ctx'' <;> simp [Ctx.fill] at t_eq₁
  rw [← t_eq₁] at t₁_redex
  cases t₁_redex

lemma decomposition_unique (t : Term) : isDecomposition t ctx₁ t₁ → isDecomposition t ctx₂ t₂
  → ctx₁ = ctx₂ ∧ t₁ = t₂ := by
  rintro ⟨t₁_redex, t_eq₁⟩ ⟨t₂_redex, t_eq₂⟩
  induction ctx₂ generalizing t ctx₁
  case hole =>
    rw [Ctx.fill] at t_eq₂
    rw [t_eq₂] at t_eq₁ t_eq₂
    exact decomposition_unique_with_hole t₂ ⟨t₁_redex, t_eq₁⟩ t₂_redex
  all_goals cases ctx₁ <;> (
    rw [t_eq₁] at t_eq₂
    simp only [Ctx.fill] at t_eq₂
    try cases t_eq₂
  )
  any_goals (
    rw [Ctx.fill] at t_eq₁
    rw [← t_eq₁] at t₁_redex
    rw [← Ctx.fill] at t_eq₁
    let ⟨ctx_eq, t_eq⟩ := decomposition_unique_with_hole t ⟨t₂_redex, t_eq₁⟩ t₁_redex
    cases ctx_eq
  )
  · rename_i ctx₂' t₂' t₁' ih ctx₁' t₁_copy t₂_copy
    generalize h₁ : Ctx.fill t₁ ctx₁' = fill₁
    generalize h₂ : Ctx.fill t₂ ctx₂' = fill₂
    rw [h₁, h₂] at t_eq₂
    cases t_eq₂
    let ⟨ctx_eq, t_eq⟩ := ih fill₁ (Eq.symm h₁) (Eq.symm h₂)
    constructor <;> simp only [ctx_eq, t_eq]
  any_goals (
    rename_i ctx₁' ih ctx₂'
    generalize h₁ : Ctx.fill t₁ ctx₂' = fill₁
    generalize h₂ : Ctx.fill t₂ ctx₁' = fill₂
    rw [h₁, h₂] at t_eq₂
    cases t_eq₂
    let ⟨ctx_eq, t_eq⟩ := ih fill₁ (Eq.symm h₁) (Eq.symm h₂)
    constructor <;> simp only [ctx_eq, t_eq]
  )

theorem smallStep_deterministic : (t ~> t₁) → (t ~> t₂) → (t₁ = t₂) := by
  rintro ⟨ctx₁, t_eq₁, t₁_eq, h_st₁⟩ ⟨ctx₂, t_eq₂, t₂_eq, h_st₂⟩
  rename_i t_redex₁ t₁_redex t_redex₂ t₂_redex
  let t_redex₁_is_redex := isRedex_iff_can_headSmallStep.mp ⟨_, h_st₁⟩
  let t_redex₂_is_redex := isRedex_iff_can_headSmallStep.mp ⟨_, h_st₂⟩
  let ⟨ctx_eq, t_redex_eq⟩ := decomposition_unique t ⟨t_redex₁_is_redex, t_eq₁⟩ ⟨t_redex₂_is_redex, t_eq₂⟩
  rw [t_redex_eq] at h_st₁
  let t₁₂_redex_eq := headSmallStep_deterministic h_st₁ h_st₂
  rw [t₁_eq, t₂_eq, ctx_eq, t₁₂_redex_eq]

def isNF (t : Term) := ∀ (t' : Term), ¬(t ~> t')

inductive isValue : Term → Prop where
  | value v : isValue (.value v)

theorem NF_unique : (t ~>* u) → (t ~>* u') → isNF u → isNF u' → u = u' := by
  sorry

theorem termination : ∀ (t : Term), ∃ t', isNF t' ∧ t ~>* t' := by
  sorry
