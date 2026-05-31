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

@[grind]
inductive IsVal : Term → Prop where
  | is_unit : IsVal Term.unit
  | is_abs : IsVal (Term.abs T t)
  | is_loc  : IsVal (Term.loc l)

def Val : Type := { t : Term // IsVal t }

abbrev Map (α : Type) : Type := ℕ → Option α
abbrev Store : Type := Map Val  -- maps store locations to values
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
def sub' (n : ℕ) (v : Term) : Term → Term
  | .var k => if k = n
    then v
    else .var k
  | .app t₁ t₂ => .app (sub' n v t₁) (sub' n v t₂)
  | .abs T t => .abs T (sub' (n+1) (shift 0 1 v) t)
  | .unit => .unit
  | .ref t => .ref (sub' n v t)
  | .deref t => .deref (sub' n v t)
  | .assn t₁ t₂ => .assn (sub' n v t₁) (sub' n v t₂)
  | .loc l => .loc l

abbrev sub := sub' 0

@[simp, grind]
def shiftDown' (n : ℕ) : Term → Term
  | .var k => if k<n then
      .var k
    else
      .var (k-1)
  | .app t₁ t₂ => .app (shiftDown' n t₁) (shiftDown' n t₂)
  | .abs T t => .abs T (shiftDown' (n+1) t)
  | .unit => .unit
  | .ref t => .ref (shiftDown' n t)
  | .deref t => .deref (shiftDown' n t)
  | .assn t₁ t₂ => .assn (shiftDown' n t₁) (shiftDown' n t₂)
  | .loc l => .loc l

abbrev shiftDown := shiftDown' 0

example : sub .unit (.app (.var 0) (.var 1)) = .app .unit (.var 1) := by simp

@[grind]
inductive SmallStep : State → State → Prop where
  | app1 :
    SmallStep ⟨t₁, μ⟩ ⟨t₁', μ'⟩ →
    SmallStep ⟨.app t₁ t₂, μ⟩ ⟨.app t₁' t₂, μ'⟩
  | app2 : (IsVal v₁) →
    SmallStep ⟨t₂, μ⟩ ⟨t₂', μ'⟩ →
    SmallStep ⟨.app v₁ t₂, μ⟩ ⟨.app v₁ t₂', μ'⟩
  | appAbs : (IsVal v₂) →
    SmallStep ⟨.app (.abs T₁₁ t₁₂) v₂, μ⟩ ⟨shiftDown (sub (shift 0 1 v₂) t₁₂), μ⟩
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

@[grind, simp]
def TyCtx.shift (Γ : TyCtx) (c : ℕ) (S : Typ) : TyCtx :=
  fun x => if x < c then Γ x else if x = c then S else Γ (x-1)

@[grind, simp]
def TyCtx.insert_head (Γ : TyCtx) (ty : Typ) : TyCtx := Γ.shift 0 ty

@[grind]
inductive Typing : TyCtx → Sgm → Term → Typ → Prop where
  | Var : (Γ x = some T) →
    Typing Γ σ (.var x) T
  | Abs : Typing (Γ.insert_head T₁) σ t₂ T₂ →
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
  | Deref : Typing Γ σ t₁ (.ref T) →
    Typing Γ σ (.deref t₁) T
  | Assign :
    Typing Γ σ t₁ (.ref T₁₁) →
    Typing Γ σ t₂ T₁₁ →
    Typing Γ σ (.assn t₁ t₂) (.unit)

lemma shiftInCtx : ∀ t Γ σ T S c, Typing Γ σ t T → Typing (Γ.shift c S) σ (shift c 1 t) T := by
  intro t
  induction t with
  | abs T_body body ih =>
    intro Γ σ T S c h
    cases h
    rename_i R meow
    rw[shift]
    have ih := ih (Γ.insert_head T_body) σ R S (c+1) meow
    have nika : ((Γ.insert_head T_body).shift (c + 1) S) = (Γ.shift c S).insert_head T_body := by
      apply funext
      intro x
      by_cases x = 0 <;> by_cases x<c+1 <;> try simp_all
      grind
      grind
    rw[nika] at ih
    exact Typing.Abs ih
  | app t₁ t₂ it₁ it₂ =>
    intro Γ σ T S c h
    cases h
    rename_i R meow nya
    rw[shift]
    constructor
    have it₂₂ := it₂ Γ σ (?app.App.T₁₁) S c meow
    exact it₁ Γ σ (R.func T) S c nya
    exact it₂ Γ σ R S c meow
  | ref t it =>
    intro Γ σ T S c h
    cases h
    rename_i R meow
    rw[shift]
    constructor
    exact it Γ σ R S c meow
  | deref t it =>
    intro Γ σ T S c h
    cases h
    rename_i meow
    rw[shift]
    constructor
    exact it Γ σ (.ref T) S c meow
  | assn t₁ t₂ it₁ it₂ =>
    intro Γ σ T S c h
    cases h
    rename_i T meow nya
    rw[shift]
    constructor
    exact it₁ Γ σ (Typ.ref ?assn.Assign.T₁₁) S c meow
    exact it₂ Γ σ T S c nya
  | _ => grind

lemma insert_head_ty : Typing Γ σ t T → Typing (Γ.insert_head S) σ (shift 0 1 t) T := by grind[shiftInCtx]

@[simp, grind]
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
    rename_i T₁ t_ty₁ T₂ t_ty₂
    suffices h : T₁ = T₂ by grind
    apply ih _ _ _ _ (And.intro t_ty₁ t_ty₂)
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

lemma substitution : ∀ t s S T Γ x σ, (Typing (Γ.insert x S) σ t T ∧ Typing Γ σ s S → Typing Γ σ (sub' x s t) T) := by
  intro t
  induction t <;> try grind
  case var n =>
    intro s S T Γ x σ ⟨h₁, h₂⟩
    by_cases n=x <;> cases h₁ <;> grind
  case abs T t ih =>
    intro s S T₁ Γ l σ ⟨abs_ty, s_ty⟩
    cases abs_ty
    rename_i R meow
    rw [sub']
    have : Typing (Γ.insert_head T) σ (sub' (l+1) (shift 0 1 s) t) R := by
      have : Typing (Map.insert (Γ.insert_head T) (l+1) S) σ t R := by
        have nika: Map.insert (Γ.insert_head T) (l+1) S = (TyCtx.insert_head (Map.insert Γ l S) T) := by
          apply funext
          intro x
          by_cases x = 0 <;> by_cases x = l+1 <;>try simp_all
          grind
        rw [nika]
        exact meow
      have : Typing (Γ.insert_head T) σ (shift 0 1 s) S := by grind[shiftInCtx]
      grind
    grind

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

@[simp, grind]
lemma shiftUpDown : shiftDown' n (shift n 1 s) = s := by
  induction s generalizing n <;> grind [shift, shiftDown']

inductive DoesNotContain : ℕ → Term → Prop
  | var : k ≠ n → DoesNotContain n (.var k)
  | app : DoesNotContain n t₁ → DoesNotContain n t₂
    → DoesNotContain n (.app t₁ t₂)
  | abs : DoesNotContain (n+1) t → DoesNotContain n (.abs T t)
  | unit : DoesNotContain n .unit
  | ref : DoesNotContain n t → DoesNotContain n (.ref t)
  | deref : DoesNotContain n t → DoesNotContain n (.deref t)
  | assn : DoesNotContain n t₁ → DoesNotContain n t₂
    → DoesNotContain n (.assn t₁ t₂)
  | loc : DoesNotContain n (.loc l)

abbrev ZeroFree := DoesNotContain 0

lemma shiftDoesNotContain : DoesNotContain n (shift n 1 s) := by
  induction s generalizing n <;> try grind [DoesNotContain, shift]

lemma shiftZeroFree : ZeroFree (shift 0 1 s) := shiftDoesNotContain

@[simp, grind]
lemma shiftDNCSucc (k : ℕ) : k ≤ n → DoesNotContain n s → DoesNotContain (n+1) (shift k 1 s) := by
  intro k_le_n n_dnc
  induction s generalizing n k <;> grind [DoesNotContain]

lemma subZeroFree : DoesNotContain n s → DoesNotContain n (sub' n s t) := by
  intro s_zf
  induction t generalizing n s <;> try grind [shiftZeroFree, DoesNotContain]

@[simp, grind]
lemma insert_head_shift_comm {Γ : TyCtx}
  : (Γ.shift k S).insert_head S' = (Γ.insert_head S').shift (k + 1) S := by
  simp
  grind [shift]

lemma nika : DoesNotContain k t → Typing (Γ.shift k S) σ t T
  → Typing Γ σ (shiftDown' k t) T := by
  intro t_zf t_ty
  induction t generalizing k Γ T <;> try grind [DoesNotContain, Typing, shift]
  case var m =>
    cases t_ty
    grind [DoesNotContain, Typing, shift]

lemma substitution' : Typing (Γ.insert_head S) σ t T
  → Typing Γ σ s S
  → Typing Γ σ (shiftDown (sub (shift 0 1 s) t)) T := by
  intro meow nya
  have bite:  Typing (Γ.insert_head S) σ (shift 0 1 s) S := by
    have unbite:= shiftInCtx s Γ σ S S 0 nya
    grind
  have not_nika : Typing (Γ.insert_head S) σ (sub' 0 (shift 0 1 s) t) T:= by
    have unbite: (Map.insert (Γ.insert_head S) 0 S) = (Γ.insert_head S):= by
      apply funext
      intro x
      by_cases x=0<;> simp_all
    rw[← unbite] at meow
    exact substitution t (shift 0 1 s) S T (Γ.insert_head S) 0 σ ⟨meow, bite ⟩
  apply nika ?_ not_nika
  apply subZeroFree
  exact shiftDoesNotContain

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
    rw [t_eq] at t_ty
  )
  case app1 t₁ μ₁ t₁' μ₁' t₂ st ih =>
    cases t_ty
    rename_i T_arg t₂_ty t₁_ty
    rw [← μ_eq] at ih
    let ⟨σ', ⟨σ_ext_h, ⟨t₁'_ty, μ'_ty⟩⟩⟩ := ih t₁_ty mu_ty rfl rfl
    exists σ'
    grind [weakening]
  case app2 v₁ t₂ μ₂ t₂' μ₂' v₁_val st ih =>
    cases t_ty
    rename_i T_arg t₂_ty v₁_ty
    let ⟨σ', ⟨σ_ext_h, ⟨t₁'_ty, μ'_ty⟩⟩⟩ := ih t₂_ty mu_ty (by grind) rfl
    exists σ'
    grind [Typing.App, weakening]
  case RefV v μ_v l v_val l_free =>
    rw [t'_eq, μ'_eq, ← μ_eq]
    rw [← μ_eq] at l_free
    clear t_eq μ_eq t'_eq μ'_eq
    cases t_ty
    rename_i T v_ty
    exists σ.insert l T
    grind [Sgm.extends, StoreWellTyped]
  case Ref t_ μ_ t_' μ_' st ih =>
    cases t_ty
    rename_i T' t__ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t__ty mu_ty (by grind) rfl
    exists σ'
    grind
  case DerefLoc μ_ v l l_loc =>
    cases t_ty
    grind [Sgm.extends, StoreWellTyped]
  case Deref t_ μ_ t_' μ_' st ih =>
    cases t_ty
    rename_i t__ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t__ty mu_ty (by grind) rfl
    exists σ'
    grind
  case Assign v l μ_ v_val =>
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
    cases t_ty
    rename_i T t₁_ty t₂_ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t₁_ty mu_ty (by grind) rfl
    exists σ'
    grind [weakening]
  case Assign2 v₁ t₂ μ₂ t₂' μ₂' v₁_val st ih =>
    cases t_ty
    rename_i T v₁_ty t₂_ty
    let ⟨σ', ⟨σ_ext_h, ⟨t_'_ty, μ'_ty⟩⟩⟩ := ih t₂_ty mu_ty (by grind) rfl
    exists σ'
    grind [Typing.Assign, weakening]
  case appAbs s S body μ_ s_val =>
    exists σ
    rw [t'_eq, μ'_eq, ←μ_eq]
    constructor
    · grind [Sgm.extends]
    · constructor
      · cases t_ty
        rename_i S meow nya
        cases nya
        apply substitution' <;> assumption
      · assumption

abbrev hasSpace (μ : Store) : Prop := ∃ l, μ l = none

theorem progress : ∀ t T σ, Typing ∅ σ t T
  → IsVal t ∨ (∀ μ, hasSpace μ → StoreWellTyped ∅ σ μ → ∃ t' μ', ⟨t, μ⟩ ~> ⟨t', μ'⟩) := by
  intro t
  induction t with
  | var x =>
    intro T σ meow
    contradiction
  | app t₁ t₂ it₁ it₂ =>
    intro T σ meow
    cases meow
    rename_i T meow nya
    have : ∀ (μ : Store), hasSpace μ → StoreWellTyped ∅ σ μ → ∃ t' μ', (t₁.app t₂, μ)~>(t', μ') := by
      intro μ bite unbite
      by_cases h₁: IsVal t₁
      · by_cases h₂ : IsVal t₂
        · cases h₁ <;> try grind
          rename_i S R s
          have : SmallStep ⟨.app (.abs R s) t₂, μ⟩ ⟨shiftDown (sub (shift 0 1 t₂) s), μ⟩ := SmallStep.appAbs h₂
          grind
        · have it₂ := it₂ T σ meow
          have ⟨t',μ',it⟩ := it₂.resolve_left h₂ μ bite unbite
          have := SmallStep.app2 h₁ it
          grind
      · rename_i T'
        have it₁ := it₁ (T.func T') σ nya
        have ⟨t',μ',it⟩ := it₁.resolve_left h₁ μ bite unbite
        have : SmallStep ⟨.app t₁ t₂, μ⟩ ⟨.app t' t₂, μ'⟩:= SmallStep.app1 it
        grind
    grind
  | ref t it =>
    intro T σ meow
    cases meow
    rename_i T meow
    have bite: ∀ (μ : Store), hasSpace μ → StoreWellTyped ∅ σ μ → ∃ t' μ', (t.ref, μ)~>(t', μ') := by
      intro μ ⟨l,il⟩ nya
      have it:= it T σ meow
      cases it
      · rename_i unbite
        have := SmallStep.RefV unbite il
        grind
      · rename_i unbite
        have ⟨t',μ',unbite⟩:=unbite μ ⟨l,il⟩ nya
        have := SmallStep.Ref unbite
        grind
    grind
  | deref t it =>
    intro T σ meow
    cases meow
    rename_i meow
    have bite: ∀ (μ : Store), hasSpace μ → StoreWellTyped ∅ σ μ → ∃ t' μ', (t.deref, μ)~>(t', μ') := by
      intro μ ⟨l,il⟩ nya
      by_cases unbite : IsVal t
      · cases meow <;> try grind
        rename_i l' meow
        have nika: ∃ v, μ l' = some v := by grind
        have ⟨v, nika⟩ := nika
        have := SmallStep.DerefLoc nika
        grind
      · have it:= it T.ref σ meow
        have ⟨t',μ',it⟩ := it.resolve_left unbite μ ⟨l,il⟩ nya
        have := SmallStep.Deref it
        grind
    grind
  | assn t₁ t₂ it₁ it₂ =>
    intro T σ meow
    cases meow
    rename_i T meow nya
    have : ∀ (μ : Store), hasSpace μ → StoreWellTyped ∅ σ μ → ∃ t' μ', (t₁.assn t₂, μ)~>(t', μ') := by
      intro μ bite unbite
      by_cases h₁: IsVal t₁
      · by_cases h₂ : IsVal t₂
        · cases h₁ <;> try grind
          rename_i l
          have : SmallStep ⟨.assn (.loc l) t₂, μ⟩ ⟨.unit, μ.insert l ⟨t₂,h₂⟩⟩ := SmallStep.Assign h₂
          grind
        · have it₂ := it₂ T σ nya
          have ⟨t',μ',it⟩ := it₂.resolve_left h₂ μ bite unbite
          have := SmallStep.Assign2 h₁ it
          grind
      · have it₁ := it₁ T.ref σ meow
        have ⟨t',μ',it⟩ := it₁.resolve_left h₁ μ bite unbite
        have : SmallStep ⟨.assn t₁ t₂, μ⟩ ⟨.assn t' t₂, μ'⟩ := SmallStep.Assign1 it
        grind
    grind
  | _ => grind
