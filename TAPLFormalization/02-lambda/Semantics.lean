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

inductive FB.SmallStep : IndexedTerm → IndexedTerm → Prop
  | appBody : FB.SmallStep t₁ t₁' → FB.SmallStep (.app t₁ t₂) (.app t₁' t₂)
  | appArg : FB.SmallStep t₂ t₂' → FB.SmallStep (.app t₁ t₂) (.app t₁ t₂')
  | absCong : FB.SmallStep t t' → FB.SmallStep (.abs t) (.abs t')
  | appAbs : FB.SmallStep (.app (.abs t₁) t₂) (subst t₂ t₁)

namespace NO
mutual
  inductive Neutral : IndexedTerm → Prop
    | freeV : Neutral (.freeV x)
    | boundV : Neutral (.boundV n)
    | app : Neutral t₁ → NF t₂ → Neutral (.app t₁ t₂)

  inductive NF : IndexedTerm → Prop
    | neutral : Neutral t → NF t
    | abs : NF t → NF (.abs t)
end

inductive SmallStep : IndexedTerm → IndexedTerm → Prop
  | appBody : SmallStep (.app t₁ t₂) t' → SmallStep (.app (.app t₁ t₂) t₃) (.app t' t₃)
  | appArg : NF t₁ → SmallStep t₂ t₂' → SmallStep (.app t₁ t₂) (.app t₁ t₂')
  | absCong : SmallStep t t' → SmallStep (.abs t) (.abs t')
  | appAbs : SmallStep (.app (.abs t₁) t₂) (subst t₂ t₁)
end NO

inductive CN.SmallStep : IndexedTerm → IndexedTerm → Prop
  | appBody : CN.SmallStep t₁ t₁' → CN.SmallStep (.app t₁ t₂) (.app t₁' t₂)
  | appAbs : SmallStep (.app (.abs t₁) t₂) (subst t₂ t₁)

inductive CV.SmallStep : IndexedTerm → IndexedTerm → Prop
  | appBody : CV.SmallStep t₁ t₁' → CV.SmallStep (.app t₁ t₂) (.app t₁' t₂)
  | appArg : CV.SmallStep t₂ t₂' → CV.SmallStep (.app (.abs t₁) t₂) (.app (.abs t₁) t₂')
  | appAbs : (s = subst (.abs t₂) t₁) → CV.SmallStep (.app (.abs t₁) (.abs t₂)) s

abbrev CV.SmallSteps := ReflTransGen' CV.SmallStep
