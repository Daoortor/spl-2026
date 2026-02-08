import TAPLFormalization.AST

inductive Ctx where
  | hole : Ctx
  | ifThenElse : Ctx → Term → Term → Ctx
  | succ : Ctx → Ctx
  | pred : Ctx → Ctx
  | isZero : Ctx → Ctx

@[reducible] def Ctx.fill (t : Term) : Ctx → Term
  | hole => t
  | ifThenElse ctx t₁ t₂ => .ifThenElse (ctx.fill t) t₁ t₂
  | succ ctx => .succ (ctx.fill t)
  | pred ctx => .pred (ctx.fill t)
  | isZero ctx => .isZero (ctx.fill t)
