import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

inductive Typ : Type where
  | Top
  | func : Typ → Typ → Typ
  | record : List (String × Typ) → Typ

inductive Term : Type where
  | var : ℕ → Term
  | app : Term → Term → Term
  | abs : Typ → Term → Term
  | record : List (String × Term) → Term
  | proj : Term → String → Term

abbrev RecLst := List (String × Term)
abbrev RecTyLst := List (String × Typ)

@[grind]
inductive IsVal : Term → Prop where
  | is_abs : IsVal (Term.abs T t)
  | record : ∀ p ∈ lts, IsVal p.snd → IsVal (.record lts)

abbrev Val : Type := { t : Term // IsVal t }

-- abbrev Map (α : Type) : Type := ℕ → Option α
abbrev TyCtx : Type := List Typ  -- maps var indices to their types

-- @[grind, simp]
-- def Map.empty  : Map α := fun _ => none

-- @[grind, simp]
-- def Map.insert (map : Map α) (key : ℕ) (val : α) :=
--   fun x => if x = key then some val else map x

-- instance : EmptyCollection (Map α) where
--   emptyCollection := Map.empty

-- @[grind, simp]
-- def truncate (ctx : TyCtx) := fun x => ctx (x+1)

-- shift all indices ≥ c by d
@[grind, simp]
def shift (c d : ℕ) (t : Term) : Term := match t with
  | .var k => if k<c
    then .var k
    else .var (k+d)
  | .app t₁ t₂ => .app (shift c d t₁) (shift c d t₂)
  | .abs ty t => .abs ty (shift (c+1) d t)
  | .record lts => .record $ lts.map (fun p => (p.fst, shift c d p.snd))
  | .proj t s => .proj (shift c d t) s
termination_by sizeOf t
decreasing_by
  any_goals grind
  induction lts <;> grind

@[grind, simp]
def sub' (n : ℕ) (v : Term) (t : Term) : Term := match t with
  | .var k => if k = n
    then v
    else .var k
  | .app t₁ t₂ => .app (sub' n v t₁) (sub' n v t₂)
  | .abs T t => .abs T (sub' (n+1) (shift 0 1 v) t)
  | .record lts => .record $ lts.map (fun p => (p.fst, sub' n v p.snd))
  | .proj t s => .proj (sub' n v t) s
termination_by sizeOf t
decreasing_by
  any_goals grind
  induction lts <;> try grind

abbrev sub := sub' 0

@[simp, grind]
def shiftDown' (n : ℕ) (t : Term) : Term := match t with
  | .var k => if k<n then
      .var k
    else
      .var (k-1)
  | .app t₁ t₂ => .app (shiftDown' n t₁) (shiftDown' n t₂)
  | .abs T t => .abs T (shiftDown' (n+1) t)
  | .record lts => .record $ lts.map (fun p => (p.fst, shiftDown' n p.snd))
  | .proj t s => .proj (shiftDown' n t) s
termination_by sizeOf t
decreasing_by
  any_goals grind
  induction lts <;> try grind

abbrev shiftDown := shiftDown' 0

@[grind]
inductive SmallStep : Term → Term → Prop where
  | app1 :
    SmallStep t₁ t₁' →
    SmallStep (.app t₁ t₂) (.app t₁' t₂)
  | app2 : (IsVal v₁) →
    SmallStep t₂ t₂' →
    SmallStep (.app v₁ t₂) (.app v₁ t₂')
  | appAbs : (IsVal v₂) →
    SmallStep (.app (.abs T₁₁ t₁₂) v₂) (shiftDown (sub (shift 0 1 v₂) t₁₂))
  | record : 

infix:90 "~>" => SmallStep

inductive Subtyping : Typ → Typ → Prop where
  | refl : Subtyping T T
  | trans : Subtyping S T → Subtyping T U → Subtyping S U
  | top : Subtyping T .Top
  | func : Subtyping T₁ S₁ → Subtyping S₂ T₂ → Subtyping (.func S₁ S₂) (.func T₁ T₂)
  | rcdWidth : Subtyping (.record (lts' :: lts)) (.record lts)
  | rcdDepth : ts₁.length = ts₂.length →
    (
      ∀ tp : Typ × Typ, tp ∈ List.zip ts₁ ts₂
      → Subtyping tp.fst tp.snd
    )
    → Subtyping (.record $ List.zip ls ts₁) (.record $ List.zip ls ts₂)
  | perm : List.Perm ts₁ ts₂ → Subtyping (.record ts₁) (.record ts₂)

infix:80 "<:" => Subtyping

@[grind]
inductive Typing : TyCtx → Term → Typ → Prop where
  | var : (Γ[x]? = some T) →
    Typing Γ (.var x) T
  | abs :
    Typing (T₁ :: Γ) t₂ T₂
    → Typing Γ (.abs T₁ t₂) (.func T₁ T₂)
  | app :
    Typing Γ t₁ (.func T₁₁ T₁₂) →
    Typing Γ t₂ T₁₁ →
    Typing Γ (.app t₁ t₂) T₁₂
  | sub : Typing Γ t S → S <: T → Typing Γ t T
  | record :
    ∀ p ∈ List.zip ts tys, Typing Γ p.fst p.snd
    → Typing Γ (.record $ List.zip ls ts) (.record $ List.zip ls tys)
  | proj :
    Typing Γ t (.record $ List.zip ls tys)
    → ⟨l, ty⟩ ∈ List.zip ls tys
    → Typing Γ (.proj t l) ty
