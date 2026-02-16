import TAPLFormalization.«02-lambda».Semantics

infixl:100 "|$|" => LambdaTerm.app
abbrev la := LambdaTerm.abs
instance : Coe String LambdaTerm where
  coe := .var

-- Church booleans, numerals, recursion, etc.
def cTrue : LambdaTerm := la "x" $ la "y" $ "x"
def cFalse : LambdaTerm := la "x" $ la "y" $ "y"
def cNot : LambdaTerm := la "b" $ la "x" $ la "y" $ "b" |$| "y" |$| "x"
def cOr : LambdaTerm := la "a" $ la "b" $ "a" |$| cTrue |$| ("b" |$| cTrue |$| cFalse)
def cAnd : LambdaTerm := la "a" $ la "b" $ "a" |$| ("b" |$| cTrue |$| cFalse) |$| cFalse

infix:100 " ~> " => CV.SmallStep
def cId : LambdaTerm := la "x" "x"

example : CV.SmallSteps (removeNames $ cId |$| (cId |$| (la "z" (cId |$| "z")))) (removeNames $ la "z" $ cId |$| "z") := by
  calc
    _ ~> (removeNames $ cId |$| (la "z" (cId |$| "z"))) := by
      simp [removeNames, removeNames', cId]
      apply CV.SmallStep.appArg
      apply CV.SmallStep.appAbs
      simp [subst, subst', addDepth]
    _ ~> _ := by
      simp [removeNames, removeNames', cId]
      apply CV.SmallStep.appAbs
      simp [subst, subst', addDepth]
