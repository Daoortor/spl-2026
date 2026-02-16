import Mathlib.Data.Nat.Notation

inductive LambdaTerm where
  | var (name : String) : LambdaTerm
  | abs (arg : String) (body : LambdaTerm) : LambdaTerm
  | app (t₁ t₂ : LambdaTerm) : LambdaTerm

def FV : LambdaTerm → Std.HashSet String
  | .var x => .ofList [x]
  | .abs arg body => (FV body).erase arg
  | .app t₁ t₂ => (FV t₁).union (FV t₂)

abbrev NamingContext := List String

inductive IndexedTerm where
  | var (k : ℕ) : IndexedTerm
  | abs (body : IndexedTerm) : IndexedTerm
  | app (t₁ t₂ : IndexedTerm) : IndexedTerm

inductive NIndexedTerm : (n : ℕ) → IndexedTerm → Prop where
  | var (k : ℕ) : (k ≤ n) → NIndexedTerm n (.var k)
  | abs (body : IndexedTerm) : NIndexedTerm (n+1) body → NIndexedTerm n (.abs body)
  | app (t₁ t₂ : IndexedTerm) : NIndexedTerm n t₁ → NIndexedTerm n t₂ → NIndexedTerm n (.app t₁ t₂)

def removeNames (Γ : NamingContext) (t : LambdaTerm) (h_in : ∀ x ∈ FV t, Γ.contains x) : {it : IndexedTerm // NIndexedTerm Γ.length it} := by
  cases t with
  | var x =>
    let it := IndexedTerm.var (Γ.findIdx (· == x))
    exists it
    constructor
    let x_in_Γ := h_in x (by simp [FV, Std.HashSet.ofList, Std.HashSet.instMembership])

    sorry
