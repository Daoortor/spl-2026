import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

inductive Typ : Type where
  | unit : Typ
  | func : Typ → Typ → Typ
  | ref : Typ → Typ

inductive Term : Type where
  | var : ℕ → Term
  | app : Term → Term → Term
  | abs : Typ → Term → Term
  | unit : Term
  | ref : Term → Term
  | deref : Term → Term
  | assn : Term → Term → Term
  | loc : ℕ → Term

inductive isVal : Term → Prop where
  | is_unit : isVal Term.unit
  | is_abs : isVal (Term.abs T t)
  | is_loc  : isVal (Term.loc l)

def Val : Type := { t : Term // isVal t }

abbrev Ctx : Type := ℕ → Option Typ
abbrev Str : Type := ℕ → Option Val
abbrev Sgm : Type := ℕ → Option Typ

@[grind, simp]
def empty  : ℕ → Option α := fun _ => none
@[grind, simp]
def insert (meow : ℕ → Option α) (n : ℕ)(nya : α) :=
  fun x => if x = n then some nya else meow x
@[grind, simp]
def truncate (meow : Ctx) :=
  fun x => meow (x+1)
def exp : Type := Term × Str

@[grind, simp]
def Shift (c d: ℕ) : Term → Term
  | .var k => if k<c
    then .var k
    else .var (k+d)
  | .app t₁ t₂ => .app (Shift c d t₁) (Shift c d t₂)
  | .abs T t =>  .abs T (Shift (c+1) d t)
  | .unit => .unit
  | .ref t => .ref (Shift c d t)
  | .deref t => .deref (Shift c d t)
  | .assn t₁ t₂ => .assn (Shift c d t₁) (Shift c d t₂)
  | .loc l => .loc l

@[grind, simp]
def Subst' (n : ℕ) (v : Term) : Term → Term
  | .var k => if k = n
    then v
    else .var k
  | .app t₁ t₂ => .app (Subst' n v t₁) (Subst' n v t₂)
  | .abs T t => .abs T (Subst' (n+1) (Shift 0 1 v) t)
  | .unit => .unit
  | .ref t => .ref (Subst' n v t)
  | .deref t => .deref (Subst' n v t)
  | .assn t₁ t₂ => .assn (Subst' n v t₁) (Subst' n v t₂)
  | .loc l => .loc l

abbrev Subst := Subst' 0

inductive SmallStep : exp → exp → Prop where
  | app1 :
    SmallStep ⟨t₁, μ⟩ ⟨t₁', μ'⟩ →
    SmallStep ⟨.app t₁ t₂, μ⟩ ⟨.app t₁' t₂, μ'⟩
  | app2 : (isVal v₁) →
    SmallStep ⟨t₂, μ⟩ ⟨t₂', μ'⟩ →
    SmallStep ⟨.app v₁ t₂, μ⟩ ⟨.app v₁ t₂', μ'⟩
  | appAbs : (isVal v₂) →
    SmallStep ⟨.app (.abs T₁₁ t₁₂) v₂, μ⟩ ⟨Subst v₂ t₁₂, μ⟩
  | RefV : (iv : isVal v₁) → (μ l = none) →
    SmallStep ⟨.ref v₁, μ⟩ ⟨.loc l, insert μ l ⟨v₁, iv⟩⟩
  | Ref :
    SmallStep ⟨t, μ⟩ ⟨t', μ'⟩ →
    SmallStep ⟨.ref t, μ⟩ ⟨.ref t', μ'⟩
  | DerefLoc {l:ℕ} : (h : μ l = some v) →
    SmallStep ⟨.deref (.loc l), μ⟩ ⟨v.1, μ⟩
  | Deref :
    SmallStep ⟨t, μ⟩ ⟨t', μ'⟩ →
    SmallStep ⟨.deref t, μ⟩ ⟨.deref t', μ'⟩
  | Assign : (iv:isVal v) →
    SmallStep ⟨.assn (.loc l) v, μ⟩ ⟨.unit, insert μ l ⟨v,iv⟩⟩
  | Assign1 :
    SmallStep ⟨t₁, μ⟩ ⟨t₁', μ'⟩ →
    SmallStep ⟨.assn t₁ t₂, μ⟩ ⟨.assn t₁' t₂, μ'⟩
  | Assign2 : (isVal v₁) →
    SmallStep ⟨t₂, μ⟩ ⟨t₂', μ'⟩ →
    SmallStep ⟨.assn v₁ t₂, μ⟩ ⟨.assn v₁ t₂', μ'⟩

@[grind]
inductive Typing : Ctx → Sgm → Term → Typ → Prop where
  | Var : (Γ x = some T) →
    Typing Γ σ (.var x) T
  | Abs : (Γ' = truncate Γ) →
    Typing (insert Γ 0 T₁) σ t₂ T₂ →
    Typing Γ' σ (.abs T₁ t₂) (.func T₁ T₂)
  | App :
    Typing Γ σ t₁ (.func T₁₁ T₁₂) →
    Typing Γ σ t₂ T₁₁ →
    Typing Γ σ (.app t₁ t₂) T₁₂
  | Unit : Typing Γ σ .unit .unit
  | Loc : σ l = some T₁ →
    Typing Γ σ (.loc l) (.ref T₁)
  | Ref : Typing Γ σ t₁ T₁ →
    Typing Γ σ (.ref t₁) (.ref T₁)
  | Deref : Typing Γ σ t₁ (.ref T) →
    Typing Γ σ (.deref t₁) T
  | Assign :
    Typing Γ σ t₁ (.ref T₁₁) →
    Typing Γ σ t₂ T₁₁ →
    Typing Γ σ (.assn t₁ t₂) (.unit)

def StrWellTyped (Γ : Ctx) (σ : Sgm) (μ : Str) : Prop :=
  ∀ l, match σ l, μ l with
    | some T, some v => Typing Γ σ v.1 T
    | none,   none   => True
    | _,      _      => False
@[grind, simp]
lemma TypeIsUnique : ∀ t Γ σ T S, (Typing Γ σ t T ∧ Typing Γ σ t S → T = S) := by
  intro t
  induction t with
  | abs T t ih =>
    intro Γ σ T S ⟨h₁,h₂⟩
    rename_i R
    cases h₁
    cases h₂
    rename_i Γ₁ R₁ h₁ e₁ Γ₂ R₂ T₂ e₂
    have eq : insert Γ₁ 0 R = insert Γ₂ 0 R := by
      have nya : ∀x:ℕ, (insert Γ₂ 0 R) x = (insert Γ₁ 0 R) x := by
        intro x
        cases x
        grind
        simp_all
        rename_i n
        have meow1: Γ₁ (n + 1) = (truncate Γ₁) (n) := by grind
        have meow2: Γ₂ (n + 1) = (truncate Γ₂) (n) := by grind
        rw[meow1, meow2]
        rw[h₁]
      grind
    grind
  | _ => grind


lemma Substitution : ∀ t s S T Γ x σ, (Typing (insert Γ x S) σ t T ∧ Typing Γ σ s S → Typing Γ σ (Subst' x s t) T) := by
  intro t
  induction t with
  | var n =>
    intro s S T Γ x σ ⟨h₁, h₂⟩
    by_cases n=x <;> cases h₁ <;> grind
  | abs T t ih =>
    intro s S T₁ Γ x σ h
    cases And.left h
    rename_i Γ' R₁ Γ₃ meow
    rw[Subst']
    let preΓ : Ctx := fun x => if x=0 then T else Γ (x-1)
    --| Abs : (Γ' = truncate Γ) →
    --Typing (insert Γ 0 T₁) σ t₂ T₂ →
    --Typing Γ' σ (.abs T₁ t₂) (.func T₁ T₂)
    -- t₂ = (Subst' (x + 1) (Shift 0 1 s) t) =
    --                          | maybe not
    have ih := ih (Shift 0 1 s) S R₁ preΓ (x+1) σ
    have nya : Typing preΓ σ (Subst' (x + 1) (Shift 0 1 s) t) R₁ := by sorry
    have meow1 : preΓ = insert preΓ 0 T := by
      have A : ∀ x, preΓ x = (insert preΓ 0 T) x := by
        intro x
        by_cases h: x=0 <;> simp[preΓ, h]
      exact funext A
    have meow2 : Γ = truncate preΓ := by
      have A : ∀ x, Γ x = (truncate preΓ) x := by
        intro x
        by_cases h: x=0 <;> simp[preΓ, h]
      exact funext A
    --exact Typing


    sorry
  | _ => grind
