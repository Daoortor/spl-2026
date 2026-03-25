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

inductive IsVal : Term → Prop where
  | is_unit : IsVal Term.unit
  | is_abs : IsVal (Term.abs T t)
  | is_loc  : IsVal (Term.loc l)

def Val : Type := { t : Term // IsVal t }

abbrev Map (α : Type) : Type := ℕ → Option α
abbrev Store : Type := Map Val
abbrev TyCtx : Type := Map Typ  -- maps var indices to their types
abbrev Sgm : Type := Map Typ  -- maps store locations to their types

def Sgm.extends (σ₁ σ₂ : Sgm) : Prop := ∀ l v, σ₂ l = some v → σ₁ l = some v

@[grind, simp]
def Map.empty  : Map α := fun _ => none

@[grind, simp]
def Map.insert (map : Map α) (key : ℕ) (val : α) :=
  fun x => if x = key then some val else map x

instance : EmptyCollection (Map α) where
  emptyCollection := Map.empty

@[grind, simp]
def truncate (ctx : TyCtx) := fun x => ctx (x+1)

def State : Type := Term × Store

@[grind, simp]
def shift (c d: ℕ) : Term → Term  -- shift all indices ≥ c by d
  | .var k => if k<c
    then .var k
    else .var (k+d)
  | .app t₁ t₂ => .app (shift c d t₁) (shift c d t₂)
  | .abs ty t => .abs ty (shift (c+1) d t)
  | .unit => .unit
  | .ref t => .ref (shift c d t)
  | .deref t => .deref (shift c d t)
  | .assn t₁ t₂ => .assn (shift c d t₁) (shift c d t₂)
  | .loc l => .loc l

@[grind, simp]
def Subst' (n : ℕ) (v : Term) : Term → Term
  | .var k => if k = n
    then v
    else .var k
  | .app t₁ t₂ => .app (Subst' n v t₁) (Subst' n v t₂)
  | .abs T t => .abs T (Subst' (n+1) (shift 0 1 v) t)
  | .unit => .unit
  | .ref t => .ref (Subst' n v t)
  | .deref t => .deref (Subst' n v t)
  | .assn t₁ t₂ => .assn (Subst' n v t₁) (Subst' n v t₂)
  | .loc l => .loc l

abbrev Subst := Subst' 0

inductive SmallStep : State → State → Prop where
  | app1 :
    SmallStep ⟨t₁, μ⟩ ⟨t₁', μ'⟩ →
    SmallStep ⟨.app t₁ t₂, μ⟩ ⟨.app t₁' t₂, μ'⟩
  | app2 : (IsVal v₁) →
    SmallStep ⟨t₂, μ⟩ ⟨t₂', μ'⟩ →
    SmallStep ⟨.app v₁ t₂, μ⟩ ⟨.app v₁ t₂', μ'⟩
  | appAbs : (IsVal v₂) →
    SmallStep ⟨.app (.abs T₁₁ t₁₂) v₂, μ⟩ ⟨Subst v₂ t₁₂, μ⟩
  | RefV : (iv : IsVal v₁) → (μ l = none) →
    SmallStep ⟨.ref v₁, μ⟩ ⟨.loc l, μ.insert l ⟨v₁, iv⟩⟩
  | Ref :
    SmallStep ⟨t, μ⟩ ⟨t', μ'⟩ →
    SmallStep ⟨.ref t, μ⟩ ⟨.ref t', μ'⟩
  | DerefLoc {l:ℕ} : (h : μ l = some v) →
    SmallStep ⟨.deref (.loc l), μ⟩ ⟨v.1, μ⟩
  | Deref :
    SmallStep ⟨t, μ⟩ ⟨t', μ'⟩ →
    SmallStep ⟨.deref t, μ⟩ ⟨.deref t', μ'⟩
  | Assign : (iv:IsVal v) →
    SmallStep ⟨.assn (.loc l) v, μ⟩ ⟨.unit, μ.insert l ⟨v,iv⟩⟩
  | Assign1 :
    SmallStep ⟨t₁, μ⟩ ⟨t₁', μ'⟩ →
    SmallStep ⟨.assn t₁ t₂, μ⟩ ⟨.assn t₁' t₂, μ'⟩
  | Assign2 : (IsVal v₁) →
    SmallStep ⟨t₂, μ⟩ ⟨t₂', μ'⟩ →
    SmallStep ⟨.assn v₁ t₂, μ⟩ ⟨.assn v₁ t₂', μ'⟩

infix:90 "~>" => SmallStep

@[grind]
inductive Typing : TyCtx → Sgm → Term → Typ → Prop where
  | Var : (Γ x = some T) →
    Typing Γ σ (.var x) T
  | Abs : (Γ' = truncate Γ) →
    Typing (Γ.insert 0 T₁) σ t₂ T₂ →
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

def StoreWellTyped (Γ : TyCtx) (σ : Sgm) (μ : Store) : Prop :=
  ∀ l, match σ l, μ l with
    | some T, some v => Typing Γ σ v.val T
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
    have eq : Γ₁.insert 0 R = Γ₂.insert 0 R := by
      have nya : ∀x:ℕ, (Γ₂.insert 0 R) x = (Γ₁.insert 0 R) x := by
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

lemma updatePreservesStoreTyping : StoreWellTyped Γ σ μ → σ l = some T
  → (v_val : IsVal v)
  → Typing Γ σ v T
  → StoreWellTyped Γ σ (μ.insert l ⟨v, v_val⟩) := by
  intro mu_ty l_ty v_val v_ty
  unfold StoreWellTyped at mu_ty ⊢
  intro l'
  unfold Map.insert
  grind

lemma weakening : Typing Γ σ t T → σ'.extends σ → Typing Γ σ' t T := by
  intro t_ty sig_ext
  induction t_ty <;> try grind [Sgm.extends]

def TyCtx.insert_head (Γ : TyCtx) (ty : Typ) : TyCtx :=
  fun x => if x = 0 then ty else Γ (x - 1)

lemma insert_head_ty : Typing Γ σ t T → Typing (Γ.insert_head S) σ (shift 0 1 t) T := by
  intro t_ty
  induction t generalizing T <;> unfold TyCtx.insert_head <;> try grind [Typing, shift]
  case app body arg body_ih arg_ih =>
    rw [shift]
    cases t_ty
    rename_i T_in arg_ty body_ty
    constructor
    · exact body_ih body_ty
    · exact arg_ih arg_ty
  case abs T_body body ih =>
    rw [shift]
    cases t_ty
    sorry
  stop sorry

lemma substitution : ∀ t s S T Γ x σ, (Typing (Γ.insert x S) σ t T ∧ Typing Γ σ s S → Typing Γ σ (Subst' x s t) T) := by
  intro t
  induction t <;> try grind
  case var n =>
    intro s S T Γ x σ ⟨h₁, h₂⟩
    by_cases n=x <;> cases h₁ <;> grind
  case abs T t ih =>
    intro s S T₁ Γ l σ ⟨abs_ty, s_ty⟩
    cases abs_ty
    rename_i Γ' T' Γ'_eq t_ty
    rw [Subst']
    let preΓ : TyCtx := Γ.insert_head T
    --| Abs : (Γ' = truncate Γ) →
    --Typing (insert Γ 0 T₁) σ t₂ T₂ →
    --Typing Γ' σ (.abs T₁ t₂) (.func T₁ T₂)
    -- t₂ = (Subst' (x + 1) (shift 0 1 s) t) =
    --                          | maybe not
    have ih := ih (shift 0 1 s) S T' preΓ (l+1) σ
    have nya : Typing preΓ σ (Subst' (l + 1) (shift 0 1 s) t) T' := by
      apply ih
      constructor
      · sorry
      · unfold preΓ
        apply insert_head_ty
        sorry
    have meow1 : preΓ = preΓ.insert 0 T := by
      have A : ∀ x, preΓ x = (preΓ.insert 0 T) x := by
        intro x
        by_cases h: x=0 <;> simp [preΓ, TyCtx.insert_head, h]
      exact funext A
    have meow2 : Γ = truncate preΓ := by
      have A : ∀ x, Γ x = (truncate preΓ) x := by
        intro x
        by_cases h: x=0 <;> simp[preΓ, TyCtx.insert_head, h]
      exact funext A
    grind

theorem preservation : Typing Γ σ t T → StoreWellTyped Γ σ μ
  → ⟨t, μ⟩ ~> ⟨t', μ'⟩
  → ∃ σ', σ'.extends σ ∧ Typing Γ σ' t' T ∧ StoreWellTyped Γ σ' μ' := by
  sorry

theorem progress : Typing ∅ σ t T
  → IsVal t ∨ (∀ μ, StoreWellTyped ∅ σ μ → ∃ t' μ', ⟨t, μ⟩ ~> ⟨t', μ'⟩) := by
  sorry
