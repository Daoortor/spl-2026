import Mathlib.Data.Nat.Notation

inductive LambdaTerm where
  | var (name : String) : LambdaTerm
  | abs (arg : String) (body : LambdaTerm) : LambdaTerm
  | app (t₁ t₂ : LambdaTerm) : LambdaTerm

def FV : LambdaTerm → Std.HashSet String
  | .var x => .ofList [x]
  | .abs arg body => (FV body).erase arg
  | .app t₁ t₂ => (FV t₁).union (FV t₂)

inductive IndexedTerm where
  | freeV (name : String) : IndexedTerm
  | boundV (index : ℕ) : IndexedTerm
  | app (t₁ t₂ : IndexedTerm) : IndexedTerm
  | abs (body : IndexedTerm) : IndexedTerm

def removeNames' (depth : ℕ) (levels : Std.HashMap String ℕ) : LambdaTerm → IndexedTerm
  | .var name => match levels[name]? with
    | .some k => .boundV k
    | .none => .freeV name
  | .abs arg body => .abs (removeNames' (depth + 1) (levels.insert arg depth) body)
  | .app t₁ t₂ => .app (removeNames' depth levels t₁) (removeNames' depth levels t₂)

def removeNames := removeNames' 0 ∅
