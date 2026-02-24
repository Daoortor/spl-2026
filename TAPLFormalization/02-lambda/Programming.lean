import TAPLFormalization.«02-lambda».Semantics
import TAPLFormalization.«02-lambda».SemanticsTheorems
import TAPLFormalization.«01-peano».Semantics

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
def cBoolEval (t : LambdaTerm) : LambdaTerm := t |$| la "x" "true" |$| la "x" "false"

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
#eval CallByValue.run 410 (removeNames $ cEq |$| (cPred |$| cNum 4) |$| (cNum 3) |$| la "x" "true" |$| la "x" "false")

def cId : LambdaTerm := la "x" "x"

def test1 := removeNames (cFst |$| (cPair |$| la "" "v" |$| la "" "w"))
def res := CallByValue.run 10 test1
#eval res

def test2 := removeNames $ cId |$| (cId |$| (la "z" (cId |$| "z")))
example : (removeNames $ cId |$| (cId |$| (la "z" (cId |$| "z")))) ~cbv~>* (removeNames $ la "z" $ cId |$| "z") := by
  calc
    _ ~cbv~> (removeNames $ cId |$| (la "z" (cId |$| "z"))) := by
      simp [removeNames, removeNames', cId]
      apply CV.SmallStep.appArg
      apply CV.SmallStep.appAbs
      simp [subst, subst', addDepth]
    _ ~cbv~> _ := by
      simp [removeNames, removeNames', cId]
      apply CV.SmallStep.appAbs
      simp [subst, subst', addDepth]

def test3 := cTrue |$| cTrue |$| cFalse
#eval CallByValue.run 2 (removeNames test3)

-- R lt bt → ∃ lz bz, LSteps lt lz ∧ isValue lz ∧ R lz bz ∧ BSteps bt bz
-- R lt bt → R lz bz → LSteps lt lz → BSteps bt bz

-- def embed' : Term → LambdaTerm
--   | .trueV => cTrue
--   | .falseV => cFalse
--   | .zero => cZero
--   | .ifThenElse c t e => cTest |$| (embed' c) |$| (embed' t) |$| (embed' e)
--   | .succ t => cSucc |$| embed' t
--   | .pred t => cPred |$| embed' t
--   | .isZero t => cIsZro |$| embed' t

-- def embed := removeNames ∘ embed'

-- def lambda_steps_of_peano_step : BooleanTerm t → t ~> t' → (removeNames $ cBoolEval $ embed' t) ~>λ (removeNames $ cBoolEval $ embed' t') := by
--   intro t_bool term_st
--   induction term_st <;> try grind [Term, BooleanTerm]
--   case IfTrue t e =>
--     simp [embed', removeNames, removeNames', cBoolEval, cTest, Std.HashMap.getElem_insert]
--   sorry
