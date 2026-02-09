import Mathlib.Data.Nat.Notation

inductive Term where
  | trueV : Term
  | falseV : Term
  | zero : Term
  | ifThenElse : Term → Term → Term → Term
  | succ : Term → Term
  | pred : Term → Term
  | isZero : Term → Term

inductive NumericValue : Term → Prop where
  | zero : NumericValue .zero
  | succ : NumericValue t → NumericValue (.succ t)

inductive Value : Term → Prop where
  | trueV : Value .trueV
  | falseV : Value .falseV
  | numericV : NumericValue t → Value t

inductive BooleanTerm : Term → Prop where
  | trueV : BooleanTerm .trueV
  | falseV : BooleanTerm .falseV
  | ifThenElse : BooleanTerm t₁ → BooleanTerm t₂ → BooleanTerm t₃ → BooleanTerm (.ifThenElse t₁ t₂ t₃)
