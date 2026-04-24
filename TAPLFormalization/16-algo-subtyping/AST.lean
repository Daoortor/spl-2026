import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation
import Std.Data.Internal.List.Defs

abbrev Label := String

structure SList where
  elems : List Label
  nodup : elems.Nodup

def SList.length (l : SList) : ℕ := l.elems.length

def SList.IsPrefix (l₁ l₂ : SList) : Prop := l₁.elems.IsPrefix (l₂.elems)

instance : GetElem SList ℕ Label (fun l i => i < l.length) where
  getElem l i h := l.elems[i]

inductive Typ : Type where
  | Top
  | arrow : Typ → Typ → Typ
  | record : SList → List Typ → Typ

def Typ.recC {motive : Typ → Sort u}
  (top : motive .Top)
  (arrow : ∀ {T₁ T₂}, motive T₁ → motive T₂ → motive (.arrow T₁ T₂))
  (record : ∀ {ls tys}, (∀ ty ∈ tys, motive ty) → motive (.record ls tys))
  : ∀ ty : Typ, motive ty
  | .Top => top
  | .arrow T₁ T₂ => arrow (recC top arrow record T₁) (recC top arrow record T₂)
  | .record ls tys => record (fun ty _ => recC top arrow record ty)

inductive WellFormed : Typ → Prop where
  | top : WellFormed .Top
  | func : WellFormed t₁ → WellFormed t₂ → WellFormed (.arrow t₁ t₂)
  | record {labels : SList} {tys : List Typ} :
    (labels.length = tys.length) →
    (∀ ty ∈ tys, WellFormed ty) →
    WellFormed (.record labels tys)

-- abbrev WellFormedTyp := {T : Typ // WellFormed T}

inductive Term where
  | var : ℕ → Term
  | app : Term → Term → Term
  | abs : Typ → Term → Term
  | record : SList → List Term → Term
  | proj : Term → String → Term

@[grind]
inductive IsVal : Term → Prop where
  | is_abs : IsVal (Term.abs T t)
  | record :
    ls.length == ts.length →
    ∀ p ∈ ts, IsVal p →
    IsVal (.record ls ts)

abbrev Val : Type := { t : Term // IsVal t }

abbrev TyCtx : Type := List Typ  -- maps var indices to their types

-- shift all indices ≥ c by d
def shift (c d : ℕ) (t : Term) : Term := match t with
  | .var k => if k<c
    then .var k
    else .var (k+d)
  | .app t₁ t₂ => .app (shift c d t₁) (shift c d t₂)
  | .abs ty t => .abs ty (shift (c+1) d t)
  | .record (ls : SList) (ts : List Term) => .record ls (ts.map (shift c d))
  | .proj t s => .proj (shift c d t) s
termination_by sizeOf t
decreasing_by
  any_goals grind
  induction ts <;> grind

@[grind, simp]
def sub' (n : ℕ) (v : Term) (t : Term) : Term := match t with
  | .var k => if k = n
    then v
    else .var k
  | .app t₁ t₂ => .app (sub' n v t₁) (sub' n v t₂)
  | .abs T t => .abs T (sub' (n+1) (shift 0 1 v) t)
  | .record ls ts => .record ls (ts.map (sub' n v))
  | .proj t s => .proj (sub' n v t) s
termination_by sizeOf t
decreasing_by
  any_goals grind
  induction ts <;> grind

abbrev sub := sub' 0

@[simp, grind]
def shiftDown' (n : ℕ) (t : Term) : Term := match t with
  | .var k => if k<n then
      .var k
    else
      .var (k-1)
  | .app t₁ t₂ => .app (shiftDown' n t₁) (shiftDown' n t₂)
  | .abs T t => .abs T (shiftDown' (n+1) t)
  | .record ls ts => .record ls (ts.map (shiftDown' n))
  | .proj t s => .proj (shiftDown' n t) s
termination_by sizeOf t
decreasing_by
  any_goals grind
  induction ts <;> grind

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
  | projRcd {ls : SList} {l : Label} (i : ℕ) :
    IsVal (.record ls ts) →
    ls[i]? = some l →
    ts[i]? = some t →
    SmallStep (.proj (.record ls ts) l) t
  | proj :
    SmallStep t₁ t₂ →
    SmallStep (.proj t₁ s) (.proj t₂ s)
  | rcd (i : ℕ) :
    (_ : ts[i]? = some t) →
    ∀ _ : j < i, IsVal (ts[j]'(by grind)) →
    SmallStep t t' →
    SmallStep (.record ls ts) (.record ls (ts.set i t'))

infix:90 "~>" => SmallStep

inductive SubT : Typ → Typ → Prop where
  | refl : WellFormed T → SubT T T
  | trans : SubT S T → SubT T U → SubT S U
  | top : WellFormed T → WellFormed T → SubT T .Top
  | arrow :
    WellFormed T₁ →
    WellFormed S₁ →
    WellFormed T₂ →
    WellFormed S₂ →
    SubT T₁ S₁ → SubT S₂ T₂ → SubT (.arrow S₁ S₂) (.arrow T₁ T₂)
  | rcdWidth :
    (∀ ty ∈ tys, WellFormed ty) →
    (∀ ty' ∈ tys', WellFormed ty') →
    tys'.IsPrefix tys →
    ls'.IsPrefix ls →
    (ls.length = tys.length) →
    (ls'.length = tys'.length) →
    SubT (.record ls tys) (.record ls' tys')
  | rcdDepth :
    (_ : ls.length = ts₁.length) →
    (_ : ls.length = ts₂.length) →
    (∀ i, (_ : i < ls.length) → SubT (ts₁[i]'(by grind)) (ts₂[i]'(by grind))) →
    SubT (.record ls ts₁) (.record ls ts₂)
  | rcdPerm {ls ls' : SList} :
    (∀ ty ∈ tys, WellFormed ty) →
    (∀ ty' ∈ tys', WellFormed ty') →
    (_ : ls.length = ls'.length) →
    (_ : ls.length = tys.length) →
    (_ : ls'.length = tys'.length) →
    (bij : Fin ls.length → Fin ls.length) →
    (∀ i, ls[bij i] = ls'[i] ∧ tys[bij i] = tys'[i]) →
    SubT (.record ls tys) (.record ls' tys')

infix:80 "<:" => SubT

@[grind]
inductive Typing : TyCtx → Term → Typ → Prop where
  | var : WellFormed T → (Γ[x]? = some T) →
    Typing Γ (.var x) T
  | abs :
    WellFormed T₁ →
    Typing (T₁ :: Γ) t₂ T₂ →
    Typing Γ (.abs T₁ t₂) (.arrow T₁ T₂)
  | app :
    Typing Γ t₁ (.arrow T₁ T₂) →
    Typing Γ t₂ T₁ →
    Typing Γ (.app t₁ t₂) T₂
  | sub : Typing Γ t S → S <: T → Typing Γ t T
  | record :
    (_ : ls.length = ts.length) →
    (_ : ls.length = tys.length) →
    (∀ i : Fin ls.length, Typing Γ ts[i] tys[i]) →
    Typing Γ (.record ls ts) (.record ls tys)
  | proj (i : Fin ls.length) :
    (_ : ls.length = tys.length) →
    Typing Γ t (.record ls tys) →
    Typing Γ (.proj t ls[i]) tys[i]

inductive AlgoSubT : Typ → Typ → Prop where
  | top : WellFormed T → AlgoSubT T .Top
  | arrow :
    WellFormed T₁ →
    WellFormed S₁ →
    WellFormed T₂ →
    WellFormed S₂ →
    AlgoSubT T₁ S₁ → AlgoSubT S₂ T₂ → AlgoSubT (.arrow S₁ S₂) (.arrow T₁ T₂)
  | rcd (ls₁ ls₂ : SList) (tys₁ tys₂ : List Typ) :
    (∀ ty ∈ tys₁, WellFormed ty) →
    (∀ ty ∈ tys₂, WellFormed ty) →
    (_ : ls₁.length = tys₁.length) →
    (_ : ls₂.length = tys₂.length) →
    (inj : Fin ls₂.length → Fin ls₁.length) →
    (∀ i, ls₁[inj i] = ls₂[i]) →
    (∀ i, AlgoSubT tys₁[inj i] tys₂[i]) →
    AlgoSubT (.record ls₁ tys₁) (.record ls₂ tys₂)

lemma AlgoSubT.refl : WellFormed T → AlgoSubT T T := by
  apply Typ.recC (motive := fun T => ∀ _, AlgoSubT T T)
  case top =>
    intro _
    exact .top .top
  case arrow =>
    intro T₁ T₂ ih₁ ih₂ wf
    cases wf
    rename_i wf₁ wf₂
    exact .arrow wf₁ wf₁ wf₂ wf₂ (ih₁ wf₁) (ih₂ wf₂)
  case record =>
    intro ls tys ih wf
    cases wf
    rename_i wfs len_eq
    exact .rcd ls ls tys tys wfs wfs len_eq len_eq id (by grind) (by grind)

@[grind]
lemma wf_of_algoSubT_left (sub : AlgoSubT T₁ T₂) : WellFormed T₁ := by
  induction sub
  case top => grind
  case arrow => constructor <;> grind
  case rcd => constructor <;> grind

@[grind]
lemma wf_of_algoSubT_right (sub : AlgoSubT T₁ T₂) : WellFormed T₂ := by
  induction sub
  case top => constructor
  case arrow => constructor <;> grind
  case rcd => constructor <;> grind

lemma AlgoSubT.trans : AlgoSubT S T → AlgoSubT T U → AlgoSubT S U := by
  apply Typ.recC (motive := fun T => ∀ S U, AlgoSubT S T → AlgoSubT T U → AlgoSubT S U)
  case top =>
    intro S' U' _ sub
    cases sub
    exact .top (by grind)
  case arrow =>
    intro U₁ U₂ ih₁ ih₂ S T sub₁ sub₂
    cases sub₂
    · exact .top (wf_of_algoSubT_left sub₁)
    · cases sub₁
      apply AlgoSubT.arrow <;> grind
  case record =>
    intro ls tys ih S U sub₁ sub₂
    cases sub₂
    · exact .top (wf_of_algoSubT_left sub₁)
    · cases sub₁
      rename Fin ls.length → _ => inj₁
      rename _ → Fin ls.length => inj₂
      constructor
      case inj => exact inj₁ ∘ inj₂
      all_goals grind

theorem algoSubT_of_subT : SubT S T → AlgoSubT S T := by
  intro sub
  induction sub
  case refl T T_wf => exact AlgoSubT.refl T_wf
  case trans _ _ _ _ _ ih₁ ih₂ => exact AlgoSubT.trans ih₁ ih₂
  case top _ T_wf _ => exact .top T_wf
  case arrow => apply AlgoSubT.arrow <;> assumption
  case rcdWidth tys tys' ls ls' tys_wf tys'_wf hpref hpref' len_eq₁ len_eq₂ =>
    apply AlgoSubT.rcd
    case inj => exact fun i => ⟨i, by grind⟩
    any_goals grind
    · intro _
      apply Eq.symm
      rw [SList.IsPrefix] at hpref'
      apply List.IsPrefix.getElem
      assumption
    · intro i
      suffices tys[i]'(by grind) = tys'[i] by grind [AlgoSubT.refl]
      apply Eq.symm
      apply List.IsPrefix.getElem
      assumption
  case rcdDepth =>
    apply AlgoSubT.rcd
    case inj => exact id
    all_goals grind [List.getElem?_of_mem]
  case rcdPerm tys tys' ls ls' tys_wf tys'_wf ls_eq tys_eq tys'_eq bij bij_h =>
    apply AlgoSubT.rcd
    case inj => exact fun i => bij ⟨i, by grind⟩
    any_goals grind
    · intro i
      exact (bij_h ⟨i, by grind⟩).left
    · intro i
      rw [(bij_h ⟨i, by grind⟩).right]
      exact AlgoSubT.refl (by grind)

theorem subT_of_algoSubT : AlgoSubT S T → SubT S T := by
  intro asub
  induction asub <;> try grind [SubT.top, SubT.arrow]
  · sorry

theorem algoSubT_iff_subT : AlgoSubT S T ↔ SubT S T :=
  .intro subT_of_algoSubT algoSubT_of_subT

inductive AlgoTyping : TyCtx → Term → Typ → Prop where
  | var : WellFormed T → (Γ[x]? = some T) →
    AlgoTyping Γ (.var x) T
  | abs :
    WellFormed T₁ →
    AlgoTyping (T₁ :: Γ) t₂ T₂ →
    AlgoTyping Γ (.abs T₁ t₂) (.arrow T₁ T₂)
  | app :
    AlgoTyping Γ t₁ (.arrow T₁₁ T₁₂) →
    AlgoTyping Γ t₂ T₂ →
    AlgoSubT T₂ T₁₁ →
    AlgoTyping Γ (.app t₁ t₂) T₁₂
  | record :
    (_ : ls.length = ts.length) →
    (_ : ls.length = tys.length) →
    (∀ i : Fin ls.length, AlgoTyping Γ ts[i] tys[i]) →
    AlgoTyping Γ (.record ls ts) (.record ls tys)
  | proj (i : Fin ls.length) :
    (_ : ls.length = tys.length) →
    AlgoTyping Γ t (.record ls tys) →
    AlgoTyping Γ (.proj t ls[i]) tys[i]

theorem typing_of_algoTyping : AlgoTyping Γ t T → Typing Γ t T := by
  intro atyp
  induction atyp <;> try grind [Typing, subT_of_algoSubT]

theorem algoTyping_of_typing : Typing Γ t T → ∃ S, S <: T ∧ AlgoTyping Γ t S := by
  sorry
