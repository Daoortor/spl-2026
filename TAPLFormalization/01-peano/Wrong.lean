import TAPLFormalization.«01-peano».Semantics
import TAPLFormalization.«01-peano».SemanticsTheorems

import Mathlib.Tactic.DefEqTransformations

namespace Term
inductive TermWrong
  | wrong : TermWrong
  | trueV : TermWrong
  | falseV : TermWrong
  | zero : TermWrong
  | ifThenElse : TermWrong → TermWrong → TermWrong → TermWrong
  | succ : TermWrong → TermWrong
  | pred : TermWrong → TermWrong
  | isZero : TermWrong → TermWrong

def embed : Term → TermWrong
  | .trueV => .trueV
  | .falseV => .falseV
  | .zero => .zero
  | .ifThenElse t₁ t₂ t₃ => .ifThenElse (embed t₁) (embed t₂) (embed t₃)
  | .succ t => .succ (embed t)
  | .pred t => .pred (embed t)
  | .isZero t => .isZero (embed t)

inductive TermWrong.IsNumericValue : TermWrong → Prop
  | zero : IsNumericValue .zero
  | succ : IsNumericValue t → IsNumericValue (.succ t)

inductive TermWrong.IsValue : TermWrong → Prop
  | trueV : IsValue .trueV
  | falseV : IsValue .falseV
  | numericV : IsNumericValue t → IsValue t

lemma embed_preserves_nv : t.IsNumericValue → (embed t).IsNumericValue := by
  intro t_nv
  induction t_nv <;> constructor
  assumption

inductive BadNat : TermWrong → Prop
  | trueV : BadNat .trueV
  | falseV : BadNat .falseV
  | wrong : BadNat .wrong

inductive BadBool : TermWrong → Prop
  | nv : t.IsNumericValue → BadBool t
  | wrong : BadBool .wrong

inductive SmallStep' : TermWrong → TermWrong → Prop
  | IfTrue : SmallStep' (.ifThenElse .trueV t₂ t₃) t₂
  | IfFalse : SmallStep' (.ifThenElse .falseV t₂ t₃) t₃
  | If : SmallStep' t₁ t₂ → SmallStep' (.ifThenElse t₁ a b) (.ifThenElse t₂ a b)
  | Succ :  SmallStep' t₁ t₂ → SmallStep' (.succ t₁) (.succ t₂)
  | PredZero : SmallStep' (.pred .zero) .zero
  | PredSucc : nv.IsNumericValue → SmallStep' (.pred (.succ nv)) nv
  | Pred : SmallStep' t₁ t₂ → SmallStep' (.pred t₁) (.pred t₂)
  | IsZeroZero : SmallStep' (.isZero .zero) .trueV
  | IsZeroSucc : nv.IsNumericValue → SmallStep' (.isZero (.succ nv)) .falseV
  | IsZero : SmallStep' t₁ t₂ → SmallStep' (.isZero t₁) (.isZero t₂)
  | IfWrong : BadBool t₁ → SmallStep' (.ifThenElse t₁ t₂ t₃) .wrong
  | SuccWrong : BadNat t → SmallStep' (.succ t) .wrong
  | PredWrong : BadNat t → SmallStep' (.pred t) .wrong
  | IsZeroWrong : BadNat t → SmallStep' (.isZero t) .wrong

abbrev SmallSteps' := ReflTransGen' SmallStep'

def Stuck (t : Term) : Prop := isNF t ∧ ¬t.IsValue

def GetsStuck (t : Term) : Prop := ∃ t', t ~>* t' ∧ Stuck t'

lemma gets_wrong_if_stuck : Stuck t → SmallSteps' (embed t) .wrong := by
  rintro ⟨t_NF, t_not_value⟩
  induction t <;> try grind [Term.IsValue, Term.IsNumericValue]
  all_goals rw [embed]
  case ifThenElse c t e ih_c ih_t ih_e =>
    have c_NF : isNF c := by
      intro c' c_st_c'
      apply t_NF
      apply SmallStep.If
      assumption
    by_cases h : c.IsValue
    case pos =>
      cases h with
      | trueV => cases t_NF t .IfTrue
      | falseV => cases t_NF e .IfFalse
      | numericV c_nv =>
        let c_bb := BadBool.nv (embed_preserves_nv c_nv)
        apply ReflTransGen'.single
        constructor
        assumption
    case neg =>
      let sts₁ := ReflTransGen'.lift (TermWrong.ifThenElse · (embed t) (embed e)) SmallStep'.If (ih_c c_NF h)
      beta_reduce at sts₁
      apply ReflTransGen'.trans' sts₁
      constructor
      exact BadBool.wrong
  case succ t ih =>
    have t_NF : isNF t := by
      intro t' t_st_t'
      apply t_NF
      constructor
      assumption
    by_cases h : t.IsValue
    case pos =>
      cases h <;> try (apply ReflTransGen'.single; repeat constructor)
      rename_i t_nv
      cases t_not_value (.numericV (.succ t_nv))
    case neg =>
      let sts₁ := ReflTransGen'.lift TermWrong.succ SmallStep'.Succ (ih t_NF h)
      apply ReflTransGen'.trans' sts₁
      constructor
      exact BadNat.wrong
  case pred t ih =>
    have t_NF : isNF t := by
      intro t' t_st_t'
      apply t_NF
      constructor
      assumption
    rename_i t_pred_NF
    by_cases h : t.IsValue
    case pos =>
      cases h <;> try (apply ReflTransGen'.single; repeat constructor)
      suffices h : False by contradiction
      rename_i t_nv
      cases t_nv
      · cases t_pred_NF _ .PredZero
      · cases t_pred_NF _ (.PredSucc (by assumption))
    case neg =>
      let sts₁ := ReflTransGen'.lift TermWrong.pred SmallStep'.Pred (ih t_NF h)
      apply ReflTransGen'.trans' sts₁
      constructor
      exact BadNat.wrong
  case isZero t ih =>
    have t_NF : isNF t := by
      intro t' t_st_t'
      apply t_NF
      constructor
      assumption
    rename_i t_pred_NF
    by_cases h : t.IsValue
    case pos =>
      cases h <;> try (apply ReflTransGen'.single; repeat constructor)
      suffices h : False by contradiction
      rename_i t_nv
      cases t_nv
      · cases t_pred_NF _ .IsZeroZero
      · cases t_pred_NF _ (.IsZeroSucc (by assumption))
    case neg =>
      let sts₁ := ReflTransGen'.lift TermWrong.isZero SmallStep'.IsZero (ih t_NF h)
      apply ReflTransGen'.trans' sts₁
      constructor
      exact BadNat.wrong

theorem getsStuck_iff_gets_wrong : GetsStuck t ↔ SmallSteps' (embed t) .wrong := by
  constructor
  · sorry
  · sorry
end Term
