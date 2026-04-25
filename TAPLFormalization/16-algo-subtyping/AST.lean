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

inductive Term where
  | var : ℕ → Term
  | app : Term → Term → Term
  | abs : Typ → Term → Term
  | record : SList → List Term → Term
  | proj : Term → String → Term

def Term.recC {motive : Term → Sort u}
  (var : ∀ {n}, motive (.var n))
  (app : ∀ {t₁ t₂}, motive t₁ → motive t₂ → motive (.app t₁ t₂))
  (abs : ∀ {t T}, motive t → motive (.abs T t))
  (record : ∀ {ls ts}, (∀ t ∈ ts, motive t) → motive (.record ls ts))
  (proj : ∀ {t s}, motive t → motive (.proj t s))
  : ∀ t : Term, motive t
  | .var n => var
  | .app t₁ t₂ => app (t₁.recC var app abs record proj) (t₂.recC var app abs record proj)
  | .abs T t => abs (t.recC var app abs record proj)
  | .record ls ts => record (fun t _ => t.recC var app abs record proj)
  | .proj t s => proj (t.recC var app abs record proj)

@[grind]
inductive IsVal : Term → Prop where
  | abs : IsVal (Term.abs T t)
  | record :
    ls.length = ts.length →
    (∀ p ∈ ts, IsVal p) →
    IsVal (.record ls ts)

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

inductive SmallStep : Term → Term → Prop where
  | app1 :
    SmallStep t₁ t₁' →
    SmallStep (.app t₁ t₂) (.app t₁' t₂)
  | app2 : IsVal v₁ →
    SmallStep t₂ t₂' →
    SmallStep (.app v₁ t₂) (.app v₁ t₂')
  | appAbs : (IsVal v₂) →
    SmallStep (.app (.abs T₁₁ t₁₂) v₂) (shiftDown (sub (shift 0 1 v₂) t₁₂))
  | projRcd (i : Fin ls.length) :
    IsVal (.record ls ts) →
    (ls.length = ts.length) →
    SmallStep (.proj (.record ls ts) l) t
  | proj :
    SmallStep t₁ t₂ →
    SmallStep (.proj t₁ s) (.proj t₂ s)
  | rcd (i : Fin ts.length) :
    (∀ j (_ : j < i), IsVal (ts[j]'(by grind))) →
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
    (∀ i : Fin ls.length, SubT ts₁[i] ts₂[i]) →
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
    any_goals grind [List.getElem?_of_mem, Fin]
    · intro ty ty_mem
      rename_i ts₁ ts₂ ls leneq₁ leneq₂ _ asubh
      let ⟨i, ⟨h_i, ty_eq⟩⟩ := List.getElem_of_mem ty_mem
      rw [← ty_eq]
      rw [← leneq₁] at h_i
      exact wf_of_algoSubT_left (asubh ⟨i, h_i⟩)
    · intro ty ty_mem
      rename_i ts₁ ts₂ ls leneq₁ leneq₂ _ asubh
      let ⟨i, ⟨h_i, ty_eq⟩⟩ := List.getElem_of_mem ty_mem
      rw [← ty_eq]
      rw [← leneq₂] at h_i
      exact wf_of_algoSubT_right (asubh ⟨i, h_i⟩)
  case rcdPerm tys tys' ls ls' tys_wf tys'_wf ls_eq tys_eq tys'_eq bij bij_h =>
    apply AlgoSubT.rcd
    case inj => exact fun i => bij ⟨i, by grind⟩
    any_goals grind
    · intro i
      exact (bij_h ⟨i, by grind⟩).left
    · intro i
      rw [(bij_h ⟨i, by grind⟩).right]
      exact AlgoSubT.refl (by grind)

lemma subT_of_rec_inj {ls ls' : SList} {tys tys' : List Typ} :
  (_ : ls.length = tys.length) →
  (_ : ls'.length = tys'.length) →
  (inj : Fin ls.length → Fin ls'.length) →
  (∀ i : Fin ls.length, ls[i] = ls'[inj i] ∧ tys[i] = tys'[inj i]) →
  (.record ls' tys') <: (.record ls tys) := by
  sorry

theorem subT_of_algoSubT : AlgoSubT S T → SubT S T := by
  intro asub
  induction asub <;> try grind [SubT.top, SubT.arrow]
  case rcd ls₁ ls₂ tys₁ tys₂ tys₁_wf tys₂_wf leneq₁ leneq₂ inj inj_eq inj_asub inj_sub =>
    sorry

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
  intro typ
  induction typ
  case var T _ _ T_wf x_mem => exact ⟨T, ⟨.refl T_wf, .var T_wf x_mem⟩⟩
  case abs T₁ Γ t₂ T₂ T₁_wf t₁_typ ih =>
    let ⟨S₂, ⟨S₂_sub, t₂_typ⟩⟩ := ih
    exists T₁.arrow S₂
    constructor
    · exact .arrow T₁_wf T₁_wf
        (wf_of_algoSubT_right $ algoSubT_of_subT S₂_sub)
        (wf_of_algoSubT_left $ algoSubT_of_subT S₂_sub)
        (.refl T₁_wf) S₂_sub
    · exact .abs T₁_wf t₂_typ
  case app Γ t₁ T₁ T₂ t₂ t₁_typ t₂_typ ih₁ ih₂ =>
    let ⟨S₁, ⟨sub₁, atyp₁⟩⟩ := ih₁
    let ⟨S₂, ⟨sub₂, atyp₂⟩⟩ := ih₂
    cases (algoSubT_of_subT sub₁)
    rename_i Γ S₁ S₂' S₁_wf S₂'_wf T₁_wf asub₁ T₂_wf asub₂
    exists S₂'
    exact ⟨
      subT_of_algoSubT asub₂,
      .app atyp₁ atyp₂ (.trans (algoSubT_of_subT sub₂) asub₁)
    ⟩
  case sub Γ t S T' typ sub ih =>
    let ⟨S', ⟨ssub, atyp⟩⟩ := ih
    exact ⟨S', ⟨.trans ssub sub, atyp⟩⟩
  case record Γ ts tys ls ts_len tys_len ts_typ ih =>
    let tys' := (List.finRange ls.length).map (fun i => (ih i).choose)
    exists .record ls tys'
    exact ⟨
      SubT.rcdDepth (ts₁ := tys') (ts₂ := tys) (ls := ls) (by grind) tys_len (by grind),
      AlgoTyping.record ts_len (by grind) (by grind)
    ⟩
  case proj Γ r ls tys i leneq typ ih =>
    let ⟨S, ⟨S_sub, atyp⟩⟩ := ih
    cases (algoSubT_of_subT S_sub)
    rename_i ls' tys' tys'_wf leneq' inj tys_wf _ inj_eq asub
    rw [← inj_eq i]
    exists tys'[inj i]
    exact ⟨
      subT_of_algoSubT $ asub i,
      .proj (inj i) leneq' atyp
    ⟩

lemma canonical_form_arrow : AlgoTyping ∅ v (.arrow T₁ T₂) → IsVal v →
  ∃ S t, v = .abs S t := by
  intro atyp v_val
  cases v_val <;> cases atyp
  exact ⟨_, ⟨_, rfl⟩⟩

lemma canonical_form_rcd : AlgoTyping ∅ v (.record ls tys) → IsVal v →
  ∃ vs,
  ls.length = vs.length ∧ (∀ p ∈ vs, IsVal p) ∧ v = .record ls vs := by
  intro atyp v_val
  cases v_val <;> cases atyp
  rename_i ts ts_val ts_leneq _ tys_leneq ih
  exists ts

theorem algo_progress : (T : Typ) → AlgoTyping ∅ t T → IsVal t ∨ ∃ t', t ~> t' := by
  apply Term.recC (motive := fun t => ∀ T, AlgoTyping ∅ t T → IsVal t ∨ ∃ t', t ~> t')
  case var => intro n _ typ; cases typ; contradiction
  case app =>
    intro t₁ t₂ ih₁ ih₂ T t_atyp
    apply Or.inr
    cases t_atyp
    rename_i T₁₁ T₂ asub t₂_atyp t₁_atyp
    have ih₁' := ih₁ _ t₁_atyp
    have ih₂' := ih₂ _ t₂_atyp
    cases ih₁'
    · cases ih₂'
      · rename_i t₁_val t₂_val
        let ⟨S, ⟨t₁₂, t₁_eq⟩⟩ := canonical_form_arrow t₁_atyp t₁_val
        rw [t₁_eq]
        exact ⟨_, SmallStep.appAbs t₂_val⟩
      · rename_i t₁_val tst
        let ⟨t₂', st⟩ := tst
        exact ⟨_, SmallStep.app2 t₁_val st⟩
    · rename_i tst
      have ⟨t₁', st⟩ := tst
      exact ⟨_, SmallStep.app1 st⟩
  case abs =>
    intro _ _ _ _ _
    exact .inl .abs
  case record =>
    intro ls ts ih T atyp
    cases atyp
    rename_i tys tys_leneq ts_leneq ts_atyp
    have ih' := fun (i : Fin ls.length) => ih ts[i] (by grind) _ (ts_atyp i)
    induction ts generalizing ls tys with
    | nil => exact .inl (.record ts_leneq (by grind))
    | cons t ts' ts_ih =>
      cases hls : ls.elems <;> try grind [SList.length]
      rename_i l ls'_list
      cases tys <;> try grind [SList.length]
      rename_i ty tys'
      rw [List.length] at ts_leneq tys_leneq
      let ls' : SList := ⟨ls'_list, by grind [SList]⟩
      have ls_leneq : ls.length = ls'.length + 1 := by grind [SList.length]
      have ts_ih' := ts_ih (fun te _ T te_atyp => ih te (by grind) _ te_atyp)
        (tys := tys') (ls := ls') (by grind [SList.length]) (by grind [SList.length])
        (fun i => ts_atyp ⟨i + 1, by grind⟩)
        (fun i => ih' ⟨i + 1, by grind⟩)
      cases h : ih' ⟨0, by grind⟩
      · rename_i t_val
        cases ts_ih'
        · exact .inl (.record (by grind) (by grind))
        · rename_i tst
          let ⟨t_', st⟩ := tst
          cases st
          apply Or.inr
          rename_i r r' r_st i val_h
          exact ⟨_, .rcd ⟨i + 1, by grind⟩ (fun j h_j => by
            let ⟨j', _⟩ := j
            cases j' <;> simp
            case zero => assumption
            case succ n _ => exact val_h ⟨n, by grind⟩ (by grind)
          ) r_st⟩
      · rename_i tst
        let ⟨t', st⟩ := tst
        exact .inr ⟨_, .rcd ⟨0, by grind⟩ (by grind) st⟩
  · intro r s ih T atyp
    cases atyp
    rename_i ls tys i leneq r_atyp
    let ih' := ih _ r_atyp
    cases ih'
    · rename_i r_val
      let ⟨vs, ⟨vs_leneq, ⟨vs_val, r_eq⟩⟩⟩ := canonical_form_rcd r_atyp r_val
      rw [r_eq]
      exact .inr ⟨vs[i]'(by grind), .projRcd i (.record vs_leneq vs_val) vs_leneq⟩
    · rename_i tst
      let ⟨r', st⟩ := tst
      exact .inr ⟨_, .proj st⟩

theorem progress : (T : Typ) → Typing ∅ t T → IsVal t ∨ ∃ t', t ~> t' := by
  intro T typ
  let ⟨S, ⟨_, atyp⟩⟩ := algoTyping_of_typing typ
  exact algo_progress S atyp
