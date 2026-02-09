import Mathlib.Logic.Relation

import TAPLFormalization.AST

inductive SmallStep : Term → Term → Prop where
  | IfTrue : SmallStep (.ifThenElse .trueV t₂ t₃) t₂
  | IfFalse : SmallStep (.ifThenElse .falseV t₂ t₃) t₃
  | If : SmallStep t₁ t₂ → SmallStep (.ifThenElse t₁ a b) (.ifThenElse t₂ a b)
  | Succ :  SmallStep t₁ t₂ → SmallStep (.succ t₁) (.succ t₂)
  | PredZero : SmallStep (.pred .zero) .zero
  | PredSucc : IsNumericValue nv → SmallStep (.pred (.succ nv)) nv
  | Pred : SmallStep t₁ t₂ → SmallStep (.pred t₁) (.pred t₂)
  | IsZeroZero : SmallStep (.isZero .zero) .trueV
  | IsZeroSucc : IsNumericValue nv → SmallStep (.isZero (.succ nv)) .falseV
  | IsZero : SmallStep t₁ t₂ → SmallStep (.isZero t₁) (.isZero t₂)

inductive SmallSteps : Term → Term → Prop where
  | refl : SmallSteps t t
  | tail : SmallStep t b → SmallSteps b u → SmallSteps t u

infix:100 "~>" => SmallStep
infix:100 "~>*" => SmallSteps
