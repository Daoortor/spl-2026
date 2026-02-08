import Mathlib.Logic.Relation

import TAPLFormalization.AST
import TAPLFormalization.Ctx

inductive HeadSmallStep : Term → Term → Prop where
  | ifTrue : HeadSmallStep (.ifThenElse (.value .trueV) t₂ t₃) t₂
  | ifFalse : HeadSmallStep (.ifThenElse (.value .falseV) t₂ t₃) t₃
  | predZero : HeadSmallStep (.pred (.value (.nv .zero))) (.value (.nv .zero))
  | predSucc : HeadSmallStep (.pred (.succ (.value (.nv n)))) (.value (.nv n))
  | isZeroZero : HeadSmallStep (.isZero (.value (.nv .zero))) (.value .trueV)
  | isZeroSucc : HeadSmallStep (.isZero (.value (.nv (.succ n)))) (.value .falseV)

inductive SmallStep : Term → Term → Prop where
  | ctx_step (ctx : Ctx) : (t₁' = ctx.fill t₁) → (t₂' = ctx.fill t₂)
    → HeadSmallStep t₁ t₂ → SmallStep t₁' t₂'

abbrev SmallSteps : Term → Term → Prop := Relation.ReflTransGen SmallStep

def SmallSteps.single : SmallStep t₁ t₂ → SmallSteps t₁ t₂ := by
  intro st
  apply Relation.ReflTransGen.single
  assumption

infix:100 "~>" => SmallStep
infix:100 "~~>" => SmallSteps
