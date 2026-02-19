import Mathlib.Logic.Relation

import TAPLFormalization.«01-peano».AST
import TAPLFormalization.«01-peano».Common

namespace Term
  inductive SmallStep : Term → Term → Prop where
    | IfTrue : SmallStep (.ifThenElse .trueV t₂ t₃) t₂
    | IfFalse : SmallStep (.ifThenElse .falseV t₂ t₃) t₃
    | If : SmallStep t₁ t₂ → SmallStep (.ifThenElse t₁ a b) (.ifThenElse t₂ a b)
    | Succ :  SmallStep t₁ t₂ → SmallStep (.succ t₁) (.succ t₂)
    | PredZero : SmallStep (.pred .zero) .zero
    | PredSucc : nv.IsNumericValue → SmallStep (.pred (.succ nv)) nv
    | Pred : SmallStep t₁ t₂ → SmallStep (.pred t₁) (.pred t₂)
    | IsZeroZero : SmallStep (.isZero .zero) .trueV
    | IsZeroSucc : nv.IsNumericValue → SmallStep (.isZero (.succ nv)) .falseV
    | IsZero : SmallStep t₁ t₂ → SmallStep (.isZero t₁) (.isZero t₂)

  abbrev SmallSteps := ReflTransGen' SmallStep
end Term

infix:100 "~>" => Term.SmallStep
infix:100 "~>*" => Term.SmallSteps
