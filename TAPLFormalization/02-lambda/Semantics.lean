import TAPLFormalization.«02-lambda».AST
import TAPLFormalization.«01-peano».Common

import Lean.Elab.App

def addDepth (k : ℕ) : IndexedTerm → IndexedTerm
  | .freeV x => .freeV x
  | .boundV n => .boundV (n+k)
  | .app t₁ t₂ => .app (addDepth k t₁) (addDepth k t₂)
  | .abs body => .abs (addDepth k body)

def subst' (depth : ℕ) (s : IndexedTerm) : IndexedTerm → IndexedTerm
  | .freeV x => .freeV x
  | .boundV n => match n with
    | .zero => addDepth depth s
    | .succ k => .boundV k
  | .app t₁ t₂ => .app (subst' depth s t₁) (subst' depth s t₂)
  | .abs body => .abs (subst' (depth+1) s body)

def subst := subst' 0

structure Semantics (T : Type u) where
  SmallStep : T → T → Prop
  isNF : T → Prop

structure DeterministicSemantics (T : Type u) extends Semantics T where
  next : T → Option T
  deterministic : SmallStep t₁ t₂ ↔ next t₁ = .some t₂
  isNF_iff_no_step : isNF t ↔ ¬(∃ t', SmallStep t t')

abbrev Semantics.SmallSteps (s : Semantics T) : T → T → Prop := ReflTransGen' s.SmallStep
def DeterministicSemantics.next_or_id (s : DeterministicSemantics T) (t : T) : T := (s.next t).elim t id
def DeterministicSemantics.run (s : DeterministicSemantics T) (gas : ℕ) (t : T) : T := gas.repeat s.next_or_id t

namespace FB
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep t₁ t₁' → SmallStep (.app t₁ t₂) (.app t₁' t₂)
    | appArg : SmallStep t₂ t₂' → SmallStep (.app t₁ t₂) (.app t₁ t₂')
    | absCong : SmallStep t t' → SmallStep (.abs t) (.abs t')
    | appAbs : s = subst t₂ t₁ → SmallStep (.app (.abs t₁) t₂) s

  mutual
    inductive Neutral : IndexedTerm → Prop
      | freeV : Neutral (.freeV x)
      | boundV : Neutral (.boundV n)
      | app : Neutral t₁ → isNF t₂ → Neutral (.app t₁ t₂)

    inductive isNF : IndexedTerm → Prop
      | neutral : Neutral t → isNF t
      | abs : isNF t → isNF (.abs t)
  end
end FB

def FullBeta : Semantics IndexedTerm where
  SmallStep := FB.SmallStep
  isNF := FB.isNF

namespace NO
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep (.app t₁ t₂) t' → SmallStep (.app (.app t₁ t₂) t₃) (.app t' t₃)
    | appArg : FB.isNF t₁ → SmallStep t₂ t₂' → SmallStep (.app t₁ t₂) (.app t₁ t₂')
    | absCong : SmallStep t t' → SmallStep (.abs t) (.abs t')
    | appAbs : s = subst t₂ t₁ → SmallStep (.app (.abs t₁) t₂) s

  mutual
    def next_app (t₁ : IndexedTerm) (t₂ : IndexedTerm) : Option IndexedTerm := match t₁, t₂ with
      | .abs t₁, t₂ => subst t₂ t₁
      | t₁, t₂ => (next t₁).elim ((.app t₁) <$> (next t₂)) (some ∘ (.app · t₂))
    termination_by (sizeOf t₁ + sizeOf t₂, 0)
    decreasing_by
      constructor
      all_goals grind [IndexedTerm, SizeOf.sizeOf, IndexedTerm._sizeOf_1]

    def next (t : IndexedTerm) : Option IndexedTerm := match t with
      | .freeV _ => none
      | .boundV _ => none
      | .abs t => .abs <$> (next t)
      | .app t₁ t₂ => next_app t₁ t₂
    termination_by (sizeOf t, 1)
  end

  lemma smallStep_deterministic : SmallStep t₁ t₂ ↔ next t₁ = .some t₂ := by
    sorry
end NO

def NormalOrder : Semantics IndexedTerm where
  SmallStep := NO.SmallStep
  isNF := FB.isNF

namespace CN
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep t₁ t₁' → SmallStep (.app t₁ t₂) (.app t₁' t₂)
    | appAbs : (s = subst t₂ t₁) → SmallStep (.app (.abs t₁) t₂) s

  inductive Neutral : IndexedTerm → Prop
    | freeV : Neutral (.freeV x)
    | boundV : Neutral (.boundV n)
    | app : Neutral t₁ → Neutral (.app t₁ t₂)

  inductive isNF : IndexedTerm → Prop
    | neutral : Neutral t → isNF t
    | abs : isNF (.abs t)

  lemma isNF_iff_no_step : isNF t ↔ ¬(∃ t', SmallStep t t') := by
    constructor
    · intro t_nf ⟨t', st⟩
      cases t_nf with
      | neutral t_ne =>
        induction t_ne generalizing t' <;> cases st
        · grind
        · contradiction
      | abs => cases st
    · intro no_st
      induction t with
      | freeV => repeat constructor
      | boundV => repeat constructor
      | app body arg body_ih arg_ih =>
        constructor
        let body_nf := by
          apply body_ih
          intro ⟨body', body_st⟩
          apply no_st
          exact ⟨body'.app arg, .appBody body_st⟩
        apply Neutral.app
        cases body <;> try grind [isNF, Neutral, subst]
        cases no_st ⟨subst arg _, SmallStep.appAbs rfl⟩
      | abs body ih => apply isNF.abs

  mutual
    def next_app : IndexedTerm → IndexedTerm → Option IndexedTerm
      | .abs t₁, t₂ => subst t₂ t₁
      | t₁, t₂ => (.app · t₂) <$> (next t₁)

    def next : IndexedTerm → Option IndexedTerm
      | .freeV _ => none
      | .boundV _ => none
      | .abs _ => none
      | .app t₁ t₂ => next_app t₁ t₂
  end

  lemma smallStep_deterministic : SmallStep t₁ t₂ ↔ next t₁ = .some t₂ := by
    constructor
    · intro st
      induction st <;> rw [next, next_app] <;> grind [next]
    · intro next_eq
      induction t₁ generalizing t₂ <;> (rw [next] at next_eq; try contradiction)
      case app body arg body_ih arg_ih =>
        fun_cases next_app <;> rw [next_app] at next_eq <;> try assumption
        all_goals grind [Option.map_eq_some_iff, SmallStep]
end CN

def CallByName : DeterministicSemantics IndexedTerm where
  SmallStep := CN.SmallStep
  isNF := CN.isNF
  next := CN.next
  deterministic := CN.smallStep_deterministic
  isNF_iff_no_step := CN.isNF_iff_no_step

namespace CV
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep t₁ t₁' → SmallStep (.app t₁ t₂) (.app t₁' t₂)
    | appArg : SmallStep t₂ t₂' → SmallStep (.app (.abs t₁) t₂) (.app (.abs t₁) t₂')
    | appAbs : (s = subst (.abs t₂) t₁) → SmallStep (.app (.abs t₁) (.abs t₂)) s

  mutual
    inductive Neutral : IndexedTerm → Prop
      | freeV : Neutral (.freeV x)
      | boundV : Neutral (.boundV n)
      | appNeutral : Neutral t₁ → Neutral (.app t₁ t₂)
      | appAbs : Neutral t₂ → Neutral (.app (.abs t₁) t₂)

    inductive isNF : IndexedTerm → Prop
      | neutral : Neutral t → isNF t
      | abs : isNF (.abs t)
  end

  lemma isNF_iff_no_step : isNF t ↔ ¬(∃ t', SmallStep t t') := by
    constructor
    · apply isNF.rec
      case motive_1 => exact fun t t_ne => ¬∃ t', SmallStep t t'
      all_goals grind [SmallStep, Neutral]
    · intro no_st
      induction t <;> try grind [isNF, Neutral, SmallStep, subst]
      case app body arg body_ih arg_ih =>
        let body_nf : isNF body := by
          apply body_ih
          intro ⟨body', body_st⟩
          exact no_st ⟨_, .appBody body_st⟩
        constructor
        cases body_nf
        · constructor
          assumption
        · apply Neutral.appAbs
          let arg_nf : isNF arg := by
            rename_i t
            apply arg_ih
            intro ⟨arg', arg_st⟩
            apply no_st ⟨_, .appArg arg_st⟩
          cases arg_nf
          · assumption
          · cases no_st ⟨_, .appAbs rfl⟩

  mutual
    def next_app (t₁ : IndexedTerm) (t₂ : IndexedTerm) : Option IndexedTerm := match t₁, t₂ with
      | .abs t₁, .abs t₂ => subst (.abs t₂) t₁
      | .abs t₁, t₂ => (.app (.abs t₁)) <$> (next t₂)
      | t₁, t₂ => (.app · t₂) <$> (next t₁)
    termination_by (sizeOf t₁ + sizeOf t₂, 0)
    decreasing_by
      constructor
      all_goals grind [IndexedTerm, SizeOf.sizeOf, IndexedTerm._sizeOf_1]

    def next (t : IndexedTerm) : Option IndexedTerm := match t with
      | .freeV _ => none
      | .boundV _ => none
      | .abs _ => none
      | .app t₁ t₂ => next_app t₁ t₂
    termination_by (sizeOf t, 1)
  end

  lemma smallStep_deterministic : SmallStep t₁ t₂ ↔ next t₁ = .some t₂ := by
    constructor
    · intro st
      induction st <;> rw [next, next_app] <;> try grind [next]
    · intro next_eq
      induction t₁ generalizing t₂ <;> (rw [next] at next_eq; try contradiction)
      case app body arg body_ih arg_ih =>
        fun_cases next_app <;> rw [next_app] at next_eq <;> try assumption
        all_goals grind [Option.map_eq_some_iff, SmallStep]
end CV

def CallByValue : DeterministicSemantics IndexedTerm where
  SmallStep := CV.SmallStep
  isNF := CV.isNF
  next := CV.next
  deterministic := CV.smallStep_deterministic
  isNF_iff_no_step := CV.isNF_iff_no_step

infix:100 " ~fb~> " => FB.SmallStep
infix:100 " ~fb~>* " => FullBeta.SmallSteps
infix:100 " ~no~> " => NO.SmallStep
infix:100 " ~no~>* " => NormalOrder.SmallSteps
infix:100 " ~cbn~> " => CN.SmallStep
infix:100 " ~cbn~>* " => CallByName.SmallSteps
infix:100 " ~cbv~> " => CV.SmallStep
infix:100 " ~cbv~>* " => CallByValue.SmallSteps
