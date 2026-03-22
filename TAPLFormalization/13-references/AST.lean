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
def Ctx.insert (μ : Ctx) (n : ℕ) (T : Typ) : Ctx :=
  fun x => if x = n then some T else μ x
def Str.insert (μ : Str) (l : ℕ) (v : Val) : Str :=
  fun x => if x = l then some v else μ x
def Sgm.insert (σ : Sgm) (l : ℕ) (T : Typ) : Sgm :=
  fun x => if x = l then some T else σ x

def exp : Type := Term × Str

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
    SmallStep ⟨.ref v₁, μ⟩ ⟨.loc l, μ.insert l ⟨v₁, iv⟩⟩
  | Ref :
    SmallStep ⟨t, μ⟩ ⟨t', μ'⟩ →
    SmallStep ⟨.ref t, μ⟩ ⟨.ref t', μ'⟩
  | DerefLoc {l:ℕ} : (h : μ l = some v) →
    SmallStep ⟨.deref (.loc l), μ⟩ ⟨v.1, μ⟩
  | Deref :
    SmallStep ⟨t, μ⟩ ⟨t', μ'⟩ →
    SmallStep ⟨.deref t, μ⟩ ⟨.deref t', μ'⟩
  | Assign : (iv:isVal v) →
    SmallStep ⟨.assn (.loc l) v, μ⟩ ⟨.unit, μ.insert l ⟨v,iv⟩⟩
  | Assign1 :
    SmallStep ⟨t₁, μ⟩ ⟨t₁', μ'⟩ →
    SmallStep ⟨.assn t₁ t₂, μ⟩ ⟨.assn t₁' t₂, μ'⟩
  | Assign2 : (isVal v₁) →
    SmallStep ⟨t₂, μ⟩ ⟨t₂', μ'⟩ →
    SmallStep ⟨.assn v₁ t₂, μ⟩ ⟨.assn v₁ t₂', μ'⟩

inductive Typing : Ctx → Sgm → Term → Typ → Prop where
  | Var : (Γ x = some T) →
    Typing Γ σ (.var x) T
  | Abs :
    Typing (Γ.insert x T₁) σ t₂ T₂ →
    Typing Γ σ (.abs T₁ t₂) (.func T₁ T₂)
  | App :
    Typing Γ σ t₁ (.func T₁₁ T₁₂) →
    Typing Γ σ t₂ T₁₁ →
    Typing Γ σ (.app t₁ t₂) T₁₂
  | Unit : Typing Γ σ .unit .unit
  | Loc : σ l = some T₁ →
    Typing Γ σ (.loc l) (.ref T₁)
  | Ref : Typing Γ σ t₁ T₁ →
    Typing Γ σ (.ref t₁) (.ref T₁)
  | Deref : Typing Γ σ t₁ T₁ →
    Typing Γ σ (.deref t₁) T₁₁
  | Assign :
    Typing Γ σ t₁ (.ref T₁₁) →
    Typing Γ σ t₂ T₁₁ →
    Typing Γ σ (.assn t₁ t₂) (.unit)
