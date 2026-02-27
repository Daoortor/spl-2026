import Mathlib.Data.Finset.Basic

inductive LambdaTerm where
  | var (name : String) : LambdaTerm
  | abs (arg : String) (body : LambdaTerm) : LambdaTerm
  | app (t₁ t₂ : LambdaTerm) : LambdaTerm
  deriving DecidableEq

-- 1. Use Finset instead of Std.HashSet for seamless interaction with Prop
def FV : LambdaTerm → Finset String
  | .var x => {x}
  | .abs arg body => (FV body).erase arg
  | .app t₁ t₂ => (FV t₁) ∪ (FV t₂)

inductive IndexedTerm where
  | freeV (name : String) : IndexedTerm
  | boundV (index : ℕ) : IndexedTerm
  | app (t₁ t₂ : IndexedTerm) : IndexedTerm
  | abs (body : IndexedTerm) : IndexedTerm
  deriving DecidableEq

-- 2. Define the extensional Environment as a pure function
@[simp]
def Env := String → Option ℕ

@[simp]
def Env.empty : Env :=
  fun _ => none
@[simp]
def Env.insert (env : Env) (k : String) (v : ℕ) : Env :=
  fun x => if x = k then some v else env x
@[simp]
def Env.erase (env : Env) (k : String) : Env := fun x => if x = k then none else env x
@[simp]
lemma Env.ext (env₁ env₂ : Env) (h : ∀ x, env₁ x = env₂ x) : env₁ = env₂ := by
  funext x
  exact h x

@[simp]
def removeNames' (depth : ℕ) (levels : Env) : LambdaTerm → IndexedTerm
  | .var name => match levels name with
    | .some k => .boundV k
    | .none => .freeV name
  | .abs arg body => .abs (removeNames' (depth + 1) (levels.insert arg depth) body)
  | .app t₁ t₂ => .app (removeNames' depth levels t₁) (removeNames' depth levels t₂)

@[simp]
def LambdaTerm.Subst (x : String) (y : String) : LambdaTerm → LambdaTerm
  | var t => if t = x then var y else if t=y then var x else var t
  | app v w => app (v.Subst x y) (w.Subst x y)
  | abs u t =>
      if u = x then abs y (t.Subst x y)
      else if u = y then abs x (t.Subst x y)
      else abs u (t.Subst x y)

inductive Alpha : LambdaTerm → LambdaTerm → Prop
  | var {x : String} : Alpha (.var x) (.var x)
  | app {v v' w w' : LambdaTerm} : Alpha v v' → Alpha w w' → Alpha (.app v w) (.app v' w')
  | abs {x x' : String} {t t' : LambdaTerm} :
      (x ∉ FV t'∨ x=x') → Alpha t (t'.Subst x x') → Alpha (.abs x t) (.abs x' t')


def removeNames : LambdaTerm → IndexedTerm :=
  removeNames' 0 Env.empty
