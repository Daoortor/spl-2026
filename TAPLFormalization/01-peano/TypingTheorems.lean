import Mathlib.Tactic.Lemma
import TAPLFormalization.«01-peano».Semantics
import TAPLFormalization.«01-peano».Typing

lemma Term.preservation : TypeJdg t ty → t ~> t' → TypeJdg t' ty := by
  intro t_jdg st
  induction st generalizing ty <;> try grind [TypeJdg]

lemma Term.progress : TypeJdg t ty → IsValue t ∨ ∃ t', t ~> t' := by
  intro t_jdg
  induction t_jdg <;> try grind [SmallStep, IsValue, IsNumericValue]
  case ifThenElse c t ty e c_jdg t_jdg ejdg c_ih t_ih e_ih =>
    apply Or.inr
    cases c_ih
    · rename_i c_v
      cases c_v <;> try grind [IsNumericValue, TypeJdg]
      · exact ⟨t, .IfTrue⟩
      · exact ⟨e, .IfFalse⟩
    · rename_i c_ih
      let ⟨c', c_st⟩ := c_ih
      exact ⟨_, .If c_st⟩
  case succ t t_jdg ih =>
    cases ih
    · rename_i t_v
      cases t_v <;> grind [TypeJdg, IsValue, IsNumericValue]
    · apply Or.inr
      rename_i t_ih
      let ⟨t', t_st⟩ := t_ih
      exact ⟨_, .Succ t_st⟩
  case pred t t_jdg ih =>
    apply Or.inr
    cases ih
    · rename_i t_v
      cases t_v <;> try grind [TypeJdg]
      rename_i t_nv
      cases t_nv
      · exact ⟨_, .PredZero⟩
      · exact ⟨_, .PredSucc (by assumption)⟩
    · rename_i t_ih
      let ⟨t', t_st⟩ := t_ih
      exact ⟨_, .Pred t_st⟩
  case isZero t t_jdg ih =>
    apply Or.inr
    cases ih
    · rename_i t_v
      cases t_v <;> try grind [TypeJdg]
      rename_i t_nv
      cases t_nv
      · exact ⟨_, .IsZeroZero⟩
      · exact ⟨_, .IsZeroSucc (by assumption)⟩
    · rename_i t_ih
      let ⟨t', t_st⟩ := t_ih
      exact ⟨_, .IsZero t_st⟩

lemma Term.termination : TypeJdg t ty → ∃ t', IsValue t' ∧ t ~>* t' := by
  intro t_jdg
  cases progress t_jdg
  · exact ⟨_, ⟨by assumption, .refl⟩⟩
  · rename_i ss
    let ⟨t', st⟩ := ss
    let pr := progress t_jdg
    cases pr
    · exact ⟨_, ⟨by assumption, .refl⟩⟩
    · let ⟨t'', ⟨t''_v, sts⟩⟩ := termination (preservation t_jdg st)
      exists t''
      constructor
      · assumption
      · exact .tail st sts
decreasing_by
  rename_i a b c d e f g
  clear a b c d e f g pr _x ty
  induction st <;> try grind
