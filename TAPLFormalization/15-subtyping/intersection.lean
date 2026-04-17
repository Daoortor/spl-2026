import Mathlib.Data.List.Basic

inductive ETyp : Type where
  | var : ℕ → ETyp
  | omega : ETyp
  | func : ETyp → ETyp → ETyp
  | inter : ETyp → ETyp → ETyp

@[grind]
inductive ESubTyp : ETyp → ETyp → Prop where
  | refl : ESubTyp x x
  | max : ESubTyp x .omega
  | refl_max : ESubTyp .omega (.func .omega .omega)
  | refl_inter : ESubTyp x (.inter x x)
  | monot_left : ESubTyp (.inter x y) x
  | monot_right : ESubTyp (.inter x y) y
  | inter_func : ESubTyp (.inter (.func x y) (.func x z)) (.func x (.inter y z))
  | trans : ESubTyp x y → ESubTyp y z → ESubTyp x z
  | inter : ESubTyp x x' → ESubTyp y y' → ESubTyp (.inter x y) (.inter x' y')
  | func : ESubTyp x' x → ESubTyp y y' → ESubTyp (.func x y) (.func x' y')
infix:90 "≤" => ESubTyp
abbrev EEquivTyp (x:ETyp) (y:ETyp) : Prop := x ≤ y ∧ y ≤ x
abbrev notEEquivTyp (x:ETyp) (y:ETyp) : Prop := ¬ EEquivTyp x y
infix:90 "∼" => EEquivTyp
infix:90 "≁" => notEEquivTyp

lemma EEquiv_refl : x ∼ x := by grind
lemma EEquiv_trans : x ∼ y → y ∼ z → x ∼ z := by grind
lemma EEquiv_symm : x ∼ y ↔ y ∼ x := by grind
lemma EEquiv_inter : x ∼ x' → y ∼ y' → (.inter x y) ∼ (.inter x' y') := by grind
lemma EEquiv_func : x ∼ x' → y ∼ y' → (.func x y) ∼ (.func x' y') := by grind

@[grind]
inductive Omega: ETyp → Prop where
  | omega : Omega .omega
  | func : Omega y → Omega (.func x y)
  | inter : Omega x → Omega y → Omega (.inter x y)
lemma OmegaFilter : ∀ meow nya, Omega meow → meow ≤ nya  → Omega nya := by
    intro meow nya bite unbite
    induction unbite <;> try grind
lemma isOmega: ∀ x, x∼.omega ↔ Omega x := by
  intro meow
  constructor
  · grind[OmegaFilter]
  · intro kar
    induction kar with
    | omega => grind
    | func A iA => grind
    | inter A B iA iB =>
      rename_i a b
      have: (.inter .omega .omega) ∼ .omega := by
        constructor
        · grind
        · grind
      grind
lemma Lemma24i : ∀ x y: ETyp,  ((.func x y) ∼ .omega) ↔ (y ∼ .omega) := by grind[isOmega]

--lemma : ∀ σ μ₁ ν₁ τ μ₂ ν₂ : ETyp, (μ₁.func ν₁).inter (μ₂.func ν₂)∼σ.func τ → σ∼ μ₁.inter μ₂ ∧ ν₁.inter ν₂≤τ := by
--
--  sorry
--
--lemma : ∀ α β, (α ≤ β → β≁.omega → ∀ μ₁ μ₂ ν₁ ν₂ σ τ, α∼(.inter (.func μ₁ ν₁) (.func μ₂ ν₂)) → β ∼ (.func σ τ) → (σ ≤ μ₁ ∧ ν₁ ≤ τ ) ∨ (σ ≤ μ₂ ∧ ν₂ ≤ τ) ∨ (σ ≤ (.inter μ₁ μ₂) ∧ (.inter ν₁ ν₂) ≤ τ)) := by
--  intro α β meow
--  induction meow with
--  | refl =>
--    rename_i x
--    intro meow μ₁ μ₂ ν₁ ν₂ σ τ nya zya
--    have : (μ₁.func ν₁).inter (μ₂.func ν₂) ∼ σ.func τ := by grind
--
--    sorry
--  | _ => sorry
--
--  sorry




def InterList : List ETyp → ETyp
  | [] => .omega
  | t :: ts => .inter t (InterList ts)

def InterSection (n : ℕ) (μ ν : ℕ → ETyp) : ETyp :=
  InterList ( (List.range n).map (fun i => .func (μ i) (ν i)) )

-- 3. The formalization of Lemma 2.4(ii)
lemma Lemma24ii {n : ℕ} {μ ν : ℕ → ETyp} {σ τ : ETyp}
  (h : InterSection n μ ν ≤ .func σ τ) :
  ∃ I : List ℕ,
    (∀ i ∈ I, i < n) ∧
    (σ ≤ InterList (I.map μ)) ∧
    (InterList (I.map ν) ≤ τ) := by
  sorry

inductive Term : Type where
  | var : ℕ → Term
  | app : Term → Term → Term
  | abs : ℕ → Term → Term

abbrev EBasis := ℕ → Option ETyp

abbrev EBasis.insert (B : EBasis)(τ : ETyp)(n : ℕ): EBasis := fun k => if k = n then some τ else B k

@[grind]
inductive EAssgn : EBasis → ETypt → Term → Prop where
  | toI {τ σ : ETyp} : EAssgn (B.insert σ x) τ M → EAssgn B (σ.func τ) (.abs x M)
  | toE {τ σ : ETyp} : EAssgn B (σ.func τ) M → EAssgn B σ N → EAssgn B τ (M.app N)
  | interI {τ σ : ETyp} : EAssgn B σ M → EAssgn B τ M → EAssgn B (σ.inter τ) M
  | Sub {τ σ : ETyp} : EAssgn B σ M → σ ≤ τ → EAssgn B τ M
  | Omega : EAssgn B ETyp.omega M

lemma interE1 {τ σ : ETyp} : EAssgn B (σ.inter τ) M → EAssgn B σ M := by grind
lemma interE2 {τ σ : ETyp} : EAssgn B (σ.inter τ) M → EAssgn B τ M := by grind

abbrev IsFilter (d : Set ETyp) : Prop := .omega ∈ d ∧ (∀ σ τ:ETyp, σ ∈ d → τ ∈ d → σ.inter τ ∈ d) ∧ (∀ σ τ:ETyp, τ ≤ σ → τ ∈ d → σ ∈ d)

lemma Lemma27i :
    ∀ B M, IsFilter {σ : ETyp | EAssgn B σ M} := by
  intro B M
  rw[IsFilter]
  constructor
  · have :  EAssgn B ETyp.omega M := by grind
    assumption
  · constructor
    · intro σ τ meow nya
      have : EAssgn B σ M := by assumption
      have : EAssgn B τ M := by assumption
      have : EAssgn B (σ.inter τ) M := by grind
      assumption
    · intro σ τ meow nya
      have : EAssgn B τ M := by assumption
      have : EAssgn B σ M := by grind
      assumption
