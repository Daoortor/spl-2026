import Mathlib.Data.Nat.Notation

inductive NumericValue where
  | zero
  | succ : NumericValue → NumericValue

inductive Value where
  | trueV : Value
  | falseV : Value
  | nv : NumericValue → Value

inductive Term where
  | value : Value → Term
  | ifThenElse : Term → Term → Term → Term
  | succ : Term → Term
  | pred : Term → Term
  | isZero : Term → Term
