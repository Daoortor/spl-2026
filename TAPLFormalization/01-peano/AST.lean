import Mathlib.Data.Nat.Notation

inductive Term where
  | trueV : Term
  | falseV : Term
  | zero : Term
  | ifThenElse : Term → Term → Term → Term
  | succ : Term → Term
  | pred : Term → Term
  | isZero : Term → Term

inductive Term.IsNumericValue : Term → Prop where
  | zero : IsNumericValue .zero
  | succ : IsNumericValue t → IsNumericValue (.succ t)

inductive Term.IsBooleanValue : Term → Prop where
  | trueV : IsBooleanValue .trueV
  | falseV : IsBooleanValue .falseV

inductive Term.IsValue : Term → Prop where
  | trueV : IsValue .trueV
  | falseV : IsValue .falseV
  | numericV : IsNumericValue t → IsValue t

inductive BooleanTerm : Term → Prop where
  | trueV : BooleanTerm .trueV
  | falseV : BooleanTerm .falseV
  | ifThenElse : BooleanTerm t₁ → BooleanTerm t₂ → BooleanTerm t₃ → BooleanTerm (.ifThenElse t₁ t₂ t₃)
