import TAPLFormalization.«01-peano».AST

inductive Term.Typ
  | int : Typ
  | bool : Typ

inductive Term.TypeJdg : Term → Typ → Prop where
  | trueV : TypeJdg .trueV .bool
  | falseV : TypeJdg .falseV .bool
  | zero : TypeJdg .zero .int
  | ifThenElse : TypeJdg c .bool → TypeJdg t ty → TypeJdg e ty → TypeJdg (.ifThenElse c t e) ty
  | succ : TypeJdg t .int → TypeJdg (.succ t) .int
  | pred : TypeJdg t .int → TypeJdg (.pred t) .int
  | isZero : TypeJdg t .int → TypeJdg (.isZero t) .bool
