import Mathlib.Logic.Relation
import Mathlib.Data.Fin.Basic

inductive type : Type where
  | bool : type
  | send : type → type → type

inductive ExpN : ℕ → Type where
  | True {n : ℕ} : ExpN n
  | False {n : ℕ} : ExpN n
  | If {n : ℕ} : ExpN n → ExpN n → ExpN n
  | bel {n : ℕ} : (x : String) → ExpN n
  | var {n : ℕ} : (k : Fin n) → ExpN n
  | app {n : ℕ} :(e₁ : ExpN n) → (e₂ : ExpN n) → ExpN n
  | abs {n : ℕ} : (T : type) →  (e : ExpN (n + 1)) → ExpN n

abbrev Exp : Type := ExpN 0

mutual
  inductive Val : Type where
    | True {n : ℕ} (ρ : EnvN n) : Val
    | False {n : ℕ} (ρ : EnvN n) : Val
    | abs {n : ℕ} (e : ExpN (n + 1)) (ρ : EnvN n) : Val

  inductive EnvN : ℕ → Type where
    | mk {n : ℕ} (map : Fin n → Val) : EnvN n
end

inductive Clo where
  | mk (n:ℕ) (e : ExpN n) (ρ : EnvN n) : Clo

def EnvN.insert {n : ℕ} (v : Val) : EnvN n → EnvN (n + 1)
  | ⟨map⟩ => ⟨Fin.cases v map⟩

def EnvN.at {n : ℕ} (ρ : EnvN n) (i : Fin n) : Val :=
  match ρ with | ⟨map⟩ => map i

inductive Cont : Type where
  | halt : Cont
  | appR (v : Val) (C : Cont) : Cont
  | appL (t : Clo) (C : Cont) : Cont

inductive State : Type where
  | eval (t : Clo) (C : Cont) : State
  | ret (v : Val) (C : Cont) : State

inductive SmallStep : State → State → Prop where
  | var {n : ℕ} (k : Fin n) (ρ : EnvN n) (C : Cont) :
      SmallStep
        (State.eval (Clo.mk n (ExpN.var k) ρ) C)
        (State.ret (ρ.at k) C)

  | abs {n : ℕ} (e : ExpN (n + 1)) (ρ : EnvN n) (C : Cont) :
      SmallStep
        (State.eval (Clo.mk n (ExpN.abs e) ρ) C)
        (State.ret (abs e ρ) C)

  | app_eval {n : ℕ} (e1 e2 : ExpN n) (ρ : EnvN n) (C : Cont) :
      SmallStep
        (State.eval (Clo.mk n (ExpN.app e1 e2) ρ) C)
        (State.eval (Clo.mk n e1 ρ) (Cont.appL (Clo.mk n e2 ρ) C))

  | app_retL {n : ℕ} (v : Val) (e2 : ExpN n) (ρ : EnvN n) (C : Cont) :
      SmallStep
        (State.ret v (Cont.appL (Clo.mk n e2 ρ) C))
        (State.eval (Clo.mk n e2 ρ) (Cont.appR v C))

  | app_retR {n : ℕ} (e : ExpN (n + 1)) (ρ : EnvN n) (v2 : Val) (C : Cont) :
      SmallStep
        (State.ret v2 (Cont.appR (abs e ρ) C))
        (State.eval (Clo.mk (n + 1) e (ρ.insert v2)) C)

abbrev SmallSteps := ReflTransGen' SmallStep

infix:100 "~>" => SmallStep
infix:100 "~>*" => SmallSteps
