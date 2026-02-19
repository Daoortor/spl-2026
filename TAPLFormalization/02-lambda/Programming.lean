import TAPLFormalization.«02-lambda».Semantics
import TAPLFormalization.«02-lambda».SemanticsTheorems

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
def cTest : LambdaTerm := la "l" $ la "m" $ la "n" $ "l" |$| "m" |$| "n"

def cPair : LambdaTerm := la "f" $ la "s" $ la "b" $ "b" |$| "f" |$| "s"
def cFst : LambdaTerm := la "p" $ "p" |$| cTrue
def cSnd : LambdaTerm := la "p" $ "p" |$| cFalse

def cZero : LambdaTerm := cFalse
def cSucc : LambdaTerm := la "n" $ la "s" $ la "z" ("s" |$| ("n" |$| "s" |$| "z"))
def cNum (n : ℕ) : LambdaTerm := n.repeat (cSucc |$| ·) cZero
def cPlus : LambdaTerm := la "m" $ la "n" $ la "s" $ la "z" ("m" |$| "s" |$| ("n" |$| "s" |$| "z"))
def cTimes : LambdaTerm := la "m" $ la "n" $ la "s" $ la "z" ("m" |$| ("n" |$| "s") |$| "z")
def cIsZro : LambdaTerm := la "n" $ "n" |$| (la "x" cFalse) |$| cTrue
def _zz : LambdaTerm := cPair |$| cZero |$| cZero
def _ss : LambdaTerm := la "p" $ cPair |$| (cSnd |$| "p") |$| (cPlus |$| (cNum 1) |$| (cSnd |$| "p"))
def cPred : LambdaTerm := la "m" $ cFst |$| ("m" |$| _ss |$| _zz)
def cSub : LambdaTerm := la "n" $ la "m" $ "n" |$| cPred |$| "m"
def cEq : LambdaTerm := la "n" $ la "m" $ cAnd |$| (cIsZro |$| (cSub |$| "m" |$| "n")) |$| (cIsZro |$| (cSub |$| "n" |$| "m"))
#eval CV.getNF 410 (removeNames $ cEq |$| (cPred |$| cNum 4) |$| (cNum 3) |$| la "x" "true" |$| la "x" "false")

infix:100 " ~> " => CV.SmallStep
def cId : LambdaTerm := la "x" "x"

def test1 := removeNames (cFst |$| (cPair |$| la "" "v" |$| la "" "w"))
def res := CV.getNF 10 test1
#eval res

def test2 := removeNames $ cId |$| (cId |$| (la "z" (cId |$| "z")))
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
