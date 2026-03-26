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

-- lemma insert_head_ty : Typing Γ σ t T → Typing (Γ.insert_head S) σ (shift 0 1 t) T := by
--   intro t_ty
--   induction t generalizing T <;> unfold TyCtx.insert_head <;> try grind [Typing, shift]
--   case app body arg body_ih arg_ih =>
--     rw [shift]
--     cases t_ty
--     rename_i T_in arg_ty body_ty
--     constructor
--     · exact body_ih body_ty
--     · exact arg_ih arg_ty
--   case abs T_body body ih =>
--     rw [shift]
--     cases t_ty
--     sorry
--   stop sorry

-- lemma substitution : ∀ t s S T Γ x σ, (Typing (Γ.insert x S) σ t T ∧ Typing Γ σ s S → Typing Γ σ (Subst' x s t) T) := by
--   intro t
--   induction t <;> try grind
--   case var n =>
--     intro s S T Γ x σ ⟨h₁, h₂⟩
--     by_cases n=x <;> cases h₁ <;> grind
--   case abs T t ih =>
--     intro s S T₁ Γ l σ ⟨abs_ty, s_ty⟩
--     cases abs_ty
--     rename_i Γ' T' Γ'_eq t_ty
--     rw [Subst']
--     let preΓ : TyCtx := Γ.insert_head T
--     --| Abs : (Γ' = truncate Γ) →
--     --Typing (insert Γ 0 T₁) σ t₂ T₂ →
--     --Typing Γ' σ (.abs T₁ t₂) (.func T₁ T₂)
--     -- t₂ = (Subst' (x + 1) (shift 0 1 s) t) =
--     --                          | maybe not
--     have ih := ih (shift 0 1 s) S T' preΓ (l+1) σ
--     have nya : Typing preΓ σ (Subst' (l + 1) (shift 0 1 s) t) T' := by
--       apply ih
--       constructor
--       · sorry
--       · unfold preΓ
--         apply insert_head_ty
--         sorry
--     have meow1 : preΓ = preΓ.insert 0 T := by
--       have A : ∀ x, preΓ x = (preΓ.insert 0 T) x := by
--         intro x
--         by_cases h: x=0 <;> simp [preΓ, TyCtx.insert_head, h]
--       exact funext A
--     have meow2 : Γ = truncate preΓ := by
--       have A : ∀ x, Γ x = (truncate preΓ) x := by
--         intro x
--         by_cases h: x=0 <;> simp[preΓ, TyCtx.insert_head, h]
--       exact funext A
--     grind

-- s_ty : Typing Γ σ s S
-- body_ty : Typing (Γ.insert_head S) σ body T
-- Γ_eq' : Map.insert Γ' 0 S = Γ.insert_head S := sorry
-- ⊢ Typing Γ σ (Subst s body) T

-- lemma substitution : Typing Γ σ s S → Typing (Γ.insert_head S) σ body T → Typing Γ σ (Subst s body) T := by
--   sorry

@[simp, grind]
lemma extends_insert : σ l = none → Sgm.extends (σ.insert l T) σ := by
  intro l_free l' v l'_some
  grind

set_option maxHeartbeats 300000

@[grind, simp]
lemma storeWellTyped_insert : Typing Γ σ v T → μ l = none → StoreWellTyped Γ σ μ
  → StoreWellTyped Γ (Map.insert σ l T) (Map.insert μ l ⟨v, v_val⟩) := by
  intro v_ty l_free mu_ty l'
  rw [Map.insert]
  split
  · rename_i _ _ T' v' T'_eq v'_eq
    let ⟨v', v'_val⟩ := v'
    split at T'_eq
    · let v_eq : v' = v := by grind
      grind [StoreWellTyped, weakening]
    · let : Typing Γ σ v' T' := by grind [mu_ty l']
      grind [weakening, StoreWellTyped]
  · trivial
  · rename_i _ _ co₁ co₂
    by_cases h : l = l'
    · apply co₁ T ⟨v, v_val⟩ <;> grind
    · cases h' : σ l' with
      | none =>
        apply co₂ <;> grind [StoreWellTyped]
      | some T' =>
        let ⟨v', _⟩ : ∃ v', μ l' = some v' := by grind [StoreWellTyped]
        apply co₁ T' v' <;> grind

theorem preservation : Typing Γ σ t T → StoreWellTyped Γ σ μ
  → ⟨t, μ⟩ ~> ⟨t', μ'⟩
  → ∃ σ', σ'.extends σ ∧ Typing Γ σ' t' T ∧ StoreWellTyped Γ σ' μ' := by
  intro t_ty mu_ty st
  generalize s₁_eq : (t, μ) = s₁
  generalize s₂_eq : (t', μ') = s₂
  rw [s₁_eq, s₂_eq] at st
  induction st generalizing t t' μ μ' T <;> (
    injection s₁_eq with t_eq μ_eq
    injection s₂_eq with t'_eq μ'_eq
  )
  case app1 t₁ μ₁ t₁' μ₁' t₂ st ih =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i T_arg t₂_ty t₁_ty
    rw [← μ_eq] at ih
    let ⟨σ', ⟨σ_ext_h, ⟨t₁'_ty, μ'_ty⟩⟩⟩ := ih t₁_ty mu_ty rfl rfl
    exists σ'
    grind [weakening]
  case app2 v₁ t₂ μ₂ t₂' μ₂' v₁_val st ih =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i T_arg t₂_ty v₁_ty
    let ⟨σ', ⟨σ_ext_h, ⟨t₁'_ty, μ'_ty⟩⟩⟩ := ih t₂_ty mu_ty (by grind) rfl
    exists σ'
    constructor
    · assumption
    · constructor
      · rw [t'_eq]
        apply Typing.App (?_ : Typing _ _ _ (T_arg.func T)) ?_
        · grind [weakening]
        · assumption
      · grind
  case RefV v μ_v l v_val l_free =>
    rw [t'_eq, μ'_eq, ← μ_eq]
    rw [← μ_eq] at l_free
    rw [t_eq] at t_ty
    clear t_eq μ_eq t'_eq μ'_eq
    cases t_ty
    rename_i T v_ty
    exists σ.insert l T
    grind [Sgm.extends, StoreWellTyped]
  case Ref t_ μ_ t_' μ_' st ih =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i T' t__ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t__ty mu_ty (by grind) rfl
    exists σ'
    grind
  case DerefLoc μ_ v l l_loc =>
    rw [t_eq] at t_ty
    cases t_ty
    grind [Sgm.extends, StoreWellTyped]
  case Deref t_ μ_ t_' μ_' st ih =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i t__ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t__ty mu_ty (by grind) rfl
    exists σ'
    grind
  case Assign v l μ_ v_val =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i T loc_ty v_ty
    cases loc_ty
    rename_i l_loc
    exists σ.insert l T
    constructor
    · grind [Sgm.extends]
    · constructor
      · grind
      · rw [← μ_eq] at μ'_eq
        rw [μ'_eq]
        let σ_eq : σ.insert l T = σ := by grind
        rw [σ_eq]
        apply updatePreservesStoreTyping <;> assumption
  case Assign1 t₁ μ₁ t₁' μ₁' t₂ st ih =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i T t₁_ty t₂_ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t₁_ty mu_ty (by grind) rfl
    exists σ'
    grind [weakening]
  case Assign2 v₁ t₂ μ₂ t₂' μ₂' v₁_val st ih =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i T v₁_ty t₂_ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t₂_ty mu_ty (by grind) rfl
    exists σ'
    constructor
    · assumption
    · constructor
      · rw [t'_eq]
        exact Typing.Assign (weakening v₁_ty σ_ext_h) t_'_ty
      · grind
  case appAbs s S body μ_ s_val =>
    rw [t_eq] at t_ty
    cases t_ty
    rename_i S s_ty arg_ty
    cases arg_ty
    rename_i Γ' Γ_eq body_ty
    unfold truncate at Γ_eq
    let Γ_eq' : Map.insert Γ' 0 S = Γ.insert_head S := by
      rw [Γ_eq]
      unfold TyCtx.insert_head Map.insert
      grind
    rw [Γ_eq'] at body_ty
    exists σ
    constructor
    · grind [Sgm.extends]
    · constructor
      · rw [t'_eq]
        sorry
      · grind

theorem progress : Typing ∅ σ t T
  → IsVal t ∨ (∀ μ, StoreWellTyped ∅ σ μ → ∃ t' μ', ⟨t, μ⟩ ~> ⟨t', μ'⟩) := by
  sorry

theorem unbites_you : False := by sorry
