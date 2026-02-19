import TAPLFormalization.«02-lambda».AST
import TAPLFormalization.«01-peano».Common

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
  next_none_iff_isNF : next t = none ↔ isNF t

def Semantics.SmallSteps (s : Semantics T) : T → T → Prop := ReflTransGen' s.SmallStep
def DeterministicSemantics.next_or_id (s : DeterministicSemantics T) (t : T) : T := (s.next t).elim t id
def DeterministicSemantics.run (s : DeterministicSemantics T) (gas : ℕ) (t : T) : T := gas.repeat s.next_or_id t

namespace FB
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep t₁ t₁' → SmallStep (.app t₁ t₂) (.app t₁' t₂)
    | appArg : SmallStep t₂ t₂' → SmallStep (.app t₁ t₂) (.app t₁ t₂')
    | absCong : SmallStep t t' → SmallStep (.abs t) (.abs t')
    | appAbs : SmallStep (.app (.abs t₁) t₂) (subst t₂ t₁)

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
    | appAbs : SmallStep (.app (.abs t₁) t₂) (subst t₂ t₁)
end NO

def NormalOrder : Semantics IndexedTerm where
  SmallStep := NO.SmallStep
  isNF := FB.isNF

namespace CN
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep t₁ t₁' → SmallStep (.app t₁ t₂) (.app t₁' t₂)
    | appAbs : SmallStep (.app (.abs t₁) t₂) (subst t₂ t₁)

  inductive Neutral : IndexedTerm → Prop
    | freeV : Neutral (.freeV x)
    | boundV : Neutral (.boundV n)
    | app : Neutral t₁ → Neutral (.app t₁ t₂)

  inductive isNF : IndexedTerm → Prop
    | neutral : Neutral t → isNF t
    | abs : isNF (.abs t)
end CN

def CallByName : Semantics IndexedTerm where
  SmallStep := CN.SmallStep
  isNF := CN.isNF

theorem CallByName.isNF_iff_no_step : CallByName.isNF t ↔ ¬(∃ t', CallByName.SmallStep t t') := by
  constructor
  · sorry
  · sorry

namespace CV
  inductive SmallStep : IndexedTerm → IndexedTerm → Prop
    | appBody : SmallStep t₁ t₁' → SmallStep (.app t₁ t₂) (.app t₁' t₂)
    | appArg : SmallStep t₂ t₂' → SmallStep (.app (.abs t₁) t₂) (.app (.abs t₁) t₂')
    | appAbs : (s = subst (.abs t₂) t₁) → SmallStep (.app (.abs t₁) (.abs t₂)) s

  abbrev SmallSteps := ReflTransGen' SmallStep

  def next : IndexedTerm → Option IndexedTerm
    | .freeV _ => none
    | .boundV _ => none
    | .abs _ => none
    | .app (.abs t₁) (.abs t₂) => subst (.abs t₂) t₁
    | .app (.abs t₁) t₂ => (.app (.abs t₁)) <$> (next t₂)
    | .app t₁ t₂ => (.app · t₂) <$> (next t₁)

  def next_or_id (t : IndexedTerm) : IndexedTerm := (next t).elim t id

  def getNF (gas : ℕ) (t : IndexedTerm) : IndexedTerm := gas.repeat next_or_id t
end CV
