import TAPLFormalization.«01-peano».Semantics
import TAPLFormalization.«02-lambda».Programming

-- BR lt bt: lt is equivalent to a purely boolean term bt
inductive BR : IndexedTerm → Term → Prop where
  | trueV : BR (.abs (.abs (.boundV 0))) .trueV
  | falseV : BR (.abs (.abs (.boundV 1))) .falseV
  | cond : BR lc bc → BR lt bt → BR le be → BR (.app (.app lc lt) le) (.ifThenElse bc bt be)

lemma br_deterministic : BR lt bt → BR lt' bt → lt = lt' := by
  intro r r'
  induction r' generalizing lt <;> grind [BR]

lemma br_defined : BooleanTerm bt → ∃ lt, BR lt bt := by
  intro bt_bt
  induction bt <;> cases bt_bt
  · exact ⟨_, by constructor⟩
  · exact ⟨_, by constructor⟩
  · rename_i c t e c_ih t_ih e_ih c_bt t_bt e_bt
    let ⟨lc, r_c⟩ := c_ih c_bt
    let ⟨lt, r_t⟩ := t_ih t_bt
    let ⟨le, r_e⟩ := e_ih e_bt
    exists (.app (.app lc lt) le)
    constructor <;> assumption

lemma bt_of_br : BR lt bt → BooleanTerm bt := by
  intro br
  induction br <;> grind [BooleanTerm]

lemma step_preserves_bt : BooleanTerm t₁ → t₁ ~> t₂ → BooleanTerm t₂ := by
  intro t₁_bt st
  induction st <;> cases t₁_bt <;> grind [BooleanTerm]

lemma subst_addDepth : subst t₁ (addDepth 1 t₂) = t₂ := by
  rw [subst]
  generalize 0 = k
  induction t₂ generalizing k <;> grind [subst', addDepth]

lemma addDepth_zero : addDepth 0 t = t := by
  induction t <;> grind [addDepth]

lemma steps_preserve_abs : .abs t ~no~>* t' → ∃ t'_b, t' = .abs t'_b := by
  intro sts
  generalize h : IndexedTerm.abs t = t₁ at sts
  induction sts generalizing t
  case refl => rw [← h]; exact ⟨t, rfl⟩
  case tail t₁ t₁' t' st sts ih =>
    rw [← h] at st
    cases st
    exact ih rfl

inductive NO'.SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep (.app t₁ t₂) t' → SmallStep (.app (.app t₁ t₂) t₃) (.app t' t₃)
    | appArg : FB.isNF t₁ → SmallStep t₂ t₂' → SmallStep (.app t₁ t₂) (.app t₁ t₂')
    | appAbs : s = subst t₂ t₁ → SmallStep (.app (.abs t₁) t₂) s

infix:100 " ~no'~> " => NO'.SmallStep
infix:100 " ~no'~>* " => ReflTransGen' NO'.SmallStep

lemma soundness_ltob_single : BR lt bt → BR lz bz → bt ~> bz → lt ~no'~>* lz := by
  intro lt_r_bt lz_r_bz b_st
  induction lt_r_bt generalizing lz bz <;> cases b_st
  case IfTrue lc lt bt le be t_r e_r t_ih e_ih c_r _ =>
    cases c_r
    let lz_eq := br_deterministic lz_r_bz t_r
    rw [lz_eq]
    calc
      _ ~no'~> .app (.abs (addDepth 1 lt)) le := .appBody (.appAbs (by simp [subst, subst']))
      _ ~no'~> _ := .appAbs (by rw [subst_addDepth])
  case IfFalse lc lt bt le be t_r e_r t_ih e_ih c_r _ =>
    cases c_r
    let lz_eq := br_deterministic lz_r_bz e_r
    rw [lz_eq]
    calc
      _ ~no'~> .app (.abs (.boundV 0)) le := .appBody (.appAbs (by simp [subst, subst']))
      _ ~no'~> _ := .appAbs (by rw [subst, subst', addDepth_zero])
  case If lc bc lt bt le be c_r t_r e_r c_ih t_ih e_ih bc' st =>
    cases lz_r_bz
    case cond c'_r t'_r e'_r =>
      let c_sts := c_ih c'_r st
      let lt_eq := br_deterministic t'_r t_r
      let le_eq := br_deterministic e'_r e_r
      rw [lt_eq, le_eq]
      clear_value c_sts
      clear c_r c_ih
      induction c_sts
      case refl => constructor
      case tail lc lc' lc'' st sts' ih => grind [IndexedTerm, NO'.SmallStep, ReflTransGen']

theorem soundness_ltob : BR lt bt → BR lz bz → bt ~>* bz → lt ~no'~>* lz := by
  intro lt_r_bt lz_r_bz b_sts
  induction b_sts generalizing lt lz
  case refl => grind [br_deterministic, ReflTransGen']
  case tail bt bt' bz b_st b_sts' ih =>
    let ⟨lt', lt'_r_bt'⟩ := br_defined (step_preserves_bt (bt_of_br lt_r_bt) b_st)
    let l_sts' := ih lt'_r_bt' lz_r_bz
    apply ReflTransGen'.trans ?_ l_sts'
    exact soundness_ltob_single lt_r_bt lt'_r_bt' b_st
