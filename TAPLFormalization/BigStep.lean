import TAPLFormalization.AST
import TAPLFormalization.Semantics
import TAPLFormalization.SemanticsTheorems

inductive BigStep : Term → Term → Prop where
  | value : v.IsValue → BigStep v v
  | ifTrue : v.IsValue → BigStep t₁ .trueV → BigStep t₂ v
    → BigStep (.ifThenElse t₁ t₂ t₃) v
  | ifFalse : v.IsValue → BigStep t₁ .falseV → BigStep t₃ v
    → BigStep (.ifThenElse t₁ t₂ t₃) v
  | succ : v.IsNumericValue → BigStep t₁ v → BigStep (.succ t₁) (.succ v)
  | predZero : BigStep t₁ .zero → BigStep (.pred t₁) .zero
  | predSucc : v.IsNumericValue → BigStep t₁ (.succ v) → BigStep (.pred t₁) v
  | isZeroZero : BigStep t₁ .zero → BigStep (.isZero t₁) .trueV
  | isZeroSucc : v.IsNumericValue → BigStep t₁ (.succ v) → BigStep (.isZero t₁) .falseV

lemma smallStep_preserves_bigStep : v.IsValue → t ~> t' → BigStep t' v → BigStep t v := by
  intro v_value t_st_t' t'_bigst_v
  induction t' generalizing t v <;>
    grind [BigStep, SmallStep, Term.IsValue, Term.IsNumericValue]

lemma bigStep_of_smallSteps : v.IsValue → t ~>* v → BigStep t v := by
  intro v_value t_sts_v
  induction t_sts_v <;> grind [BigStep, smallStep_preserves_bigStep]

lemma smallSteps_of_bigStep : v.IsValue → BigStep t v → t ~>* v := by
  intro v_value t_bigst_v
  induction t_bigst_v
  case value => constructor
  case ifTrue v_value t₁_bst_trueV t₂_bst_v ih_trueV ih_v =>
    rename_i t₁ t₂ v t₃ _
    let t₁_sts_trueV := ih_trueV (by constructor)
    let t₂_sts_v := ih_v v_value
    let sts₁ : t₁.ifThenElse t₂ t₃ ~>* .ifThenElse .trueV t₂ t₃ := ReflTransGen'.lift
      (Term.ifThenElse · t₂ t₃) SmallStep.If t₁_sts_trueV
    let sts₂ : t₁.ifThenElse t₂ t₃ ~>* t₂ := ReflTransGen'.trans' sts₁ .IfTrue
    exact ReflTransGen'.trans sts₂ t₂_sts_v
  case ifFalse v_value t₁_bigst_falseV t₂_bst_v ih_falseV ih_v =>
    rename_i t₁ t₂ v t₃ _
    let t₁_sts_falseV := ih_falseV (by constructor)
    let t₂_sts_v := ih_v v_value
    let sts₁ : t₁.ifThenElse t₃ t₂ ~>* .ifThenElse .falseV t₃ t₂ := ReflTransGen'.lift
      (Term.ifThenElse · t₃ t₂) SmallStep.If t₁_sts_falseV
    let sts₂ : t₁.ifThenElse t₃ t₂ ~>* t₂ := ReflTransGen'.trans' sts₁ .IfFalse
    exact ReflTransGen'.trans sts₂ t₂_sts_v
  case succ v_value t_bst_v ih =>
    apply ReflTransGen'.lift Term.succ SmallStep.Succ
    apply ih
    cases v_value
    rename_i v_nv
    cases v_nv
    constructor
    assumption
  case predZero t_st_zero ih =>
    let sts₁ := ReflTransGen'.lift Term.pred SmallStep.Pred
      (ih (by repeat constructor))
    apply ReflTransGen'.trans' sts₁
    constructor
  case predSucc v_nv t_bst_v_succ ih =>
    let sts₁ := ReflTransGen'.lift Term.pred SmallStep.Pred
      (ih (by constructor; constructor; assumption))
    apply ReflTransGen'.trans' sts₁
    constructor
    assumption
  case isZeroZero t_bst_zero ih =>
    let sts₁ := ReflTransGen'.lift Term.isZero SmallStep.IsZero
      (ih (by repeat constructor))
    apply ReflTransGen'.trans' sts₁
    constructor
  case isZeroSucc v_nv t_bst_v_succ ih =>
    let sts₁ := ReflTransGen'.lift Term.isZero SmallStep.IsZero
      (ih (by constructor; constructor; assumption))
    apply ReflTransGen'.trans' sts₁
    constructor
    assumption

theorem bigStep_iff_smallSteps : v.IsValue → (BigStep t v ↔ t ~>* v) := by
  intro v_value
  constructor
  · exact smallSteps_of_bigStep v_value
  · exact bigStep_of_smallSteps v_value
