import TAPLFormalization.AST
import TAPLFormalization.Semantics

inductive BigStep : Term → Term → Prop where
  | value : IsValue v → BigStep v v
  | ifTrue : IsValue v → BigStep t₁ .trueV → BigStep t₂ v
    → BigStep (.ifThenElse t₁ t₂ t₃) v
  | ifFalse : IsValue v → BigStep t₁ .falseV → BigStep t₃ v → BigStep (.ifThenElse t₁ t₂ t₃) v
  | succ : IsNumericValue v → BigStep t₁ v → BigStep (.succ t₁) (.succ v)
  | predZero : BigStep t₁ .zero → BigStep (.pred t₁) .zero
  | predSucc : IsNumericValue v → BigStep t₁ (.succ v) → BigStep (.pred t₁) v
  | isZeroZero : BigStep t₁ .zero → BigStep (.isZero t₁) .trueV
  | isZeroSucc : IsNumericValue v → BigStep t₁ (.succ v) → BigStep (.isZero t₁) .falseV

lemma smallStep_preserves_bigStep : IsValue v → t ~> t' → BigStep t' v → BigStep t v := by
  intro v_value t_st_t' t'_bigst_v
  induction t' generalizing t v <;>
    grind [BigStep, SmallStep, IsValue, IsNumericValue]

lemma bigStep_of_smallSteps : IsValue v → t ~>* v → BigStep t v := by
  intro v_value t_sts_v
  induction t_sts_v <;> grind [BigStep, smallStep_preserves_bigStep]

lemma smallSteps_of_bigStep : IsValue v → BigStep t v → t ~>* v := by
  sorry

theorem bigStep_iff_smallSteps : IsValue v → (BigStep t v ↔ t ~>* v) := by
  intro v_value
  constructor
  · exact smallSteps_of_bigStep v_value
  · exact bigStep_of_smallSteps v_value
