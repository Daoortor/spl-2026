import TAPLFormalization.«02-lambda».Semantics

def Change (x : String) (x' : String) (s : Env) : Env :=
  match s x, s x' with
  | some v, some v' => (s.insert x v').insert x' v
  | some v, none    => (s.erase x).insert x' v
  | none,   some v' => (s.erase x').insert x v'
  | none,   none    => s

lemma Ord2 : ∀ t : LambdaTerm, ∀ x x' : String, LambdaTerm.Subst x x' (LambdaTerm.Subst x x' t) = t := by
  intro t x x'
  induction t
  case var y =>
    by_cases h₁ : y = x <;> by_cases h₂ : y = x' <;> simp_all [LambdaTerm.Subst, Ne.symm]
  case app t₁ t₂ ih₁ ih₂ =>
    simp_all [LambdaTerm.Subst]
  case abs u body ih =>
    by_cases h₁ : u = x <;> by_cases h₂ : u = x' <;> by_cases h₃ : x = x' <;> simp_all [LambdaTerm.Subst, Ne.symm]

lemma ChangeIsSane: ∀ levels: Env, ∀ x x':String, Change x x' levels = Change x' x levels := by
  intro levels x x'
  funext k
  by_cases h_xx : x = x' <;> by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]

@[simp]
lemma InterChange: ∀ levels: Env, ∀ x x': String, ∀d:ℕ,((Change x x' levels).insert x' d) = (Change x x' (levels.insert x d)) := by
  intro levels x x' d
  funext k
  by_cases h_xx : x = x' <;> by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]
@[simp]
lemma InterChangeX: ∀ levels: Env, ∀ x x': String, ∀d:ℕ,((Change x x' levels).insert x d) = (Change x x' (levels.insert x' d)) := by
  intro levels x x' d
  funext k
  by_cases h_xx : x = x' <;> by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]
@[simp]
lemma TransChange: ∀ levels: Env, ∀ x x' arg: String, ∀d:ℕ,arg≠x→ arg≠ x' → ((Change x x' levels).insert arg d) = (Change x x' (levels.insert arg d)) := by
  intro levels x x' arg d A B
  funext k
  by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]

@[simp]
lemma SubstIsSane: ∀ t: LambdaTerm, ∀ x : String, t.Subst x x = t := by
  intro t x
  induction t
  case var y =>
    by_cases h : y = x <;> simp_all [LambdaTerm.Subst]
  case app t₁ t₂ ih₁ ih₂ =>
    simp_all [LambdaTerm.Subst]
  case abs u body ih =>
    by_cases h : u = x <;> simp_all [LambdaTerm.Subst]

lemma ChangeOfChanges : ∀t : LambdaTerm, ∀ x x' : String, ∀ d: Nat, ∀ levels: Env, (x∉ FV t) ∨ (∃ v, levels x = some v) →  (x'∉ FV t)∨  (∃ v, levels x' = some v) → removeNames' d (Change x x' levels) (t.Subst x x') = removeNames' d levels t := by
  intro t x x'
  induction t
  case var y =>
    intro d levels A B
    by_cases h₁ : y = x
    · rcases A with hA | hA <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [FV, Change]
    · by_cases h₂ : y = x'
      · rcases B with hB | hB <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [FV, Change, Ne.symm]
      · cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change]
  case app r₁ r₂ ihh1 ihh2=>
    intro d levels A B
    let L : ∀x:String, ∀ t₁ t₂:LambdaTerm, ¬ x∈ FV (t₁.app t₂) → ¬ x ∈ FV t₁:= by
      intro x t₁ t₂ C x_in
      rw [FV] at C
      apply C
      exact Finset.mem_union_left (FV t₂) x_in
    let R : ∀x:String, ∀ t₁ t₂:LambdaTerm, ¬ x∈ FV (t₁.app t₂) → ¬ x ∈ FV t₂:= by
      intro x t₁ t₂ C x_in
      rw [FV] at C
      apply C
      exact Finset.mem_union_right (FV t₁) x_in
    let ihh1 := ihh1 d levels
    let ihh2 := ihh2 d levels
    cases A with
    | inl hA =>
      cases B with
      | inl hB =>
        let ihh1 := ihh1 (Or.inl (L x r₁ r₂ hA)) (Or.inl (L x' r₁ r₂ hB))
        let ihh2 := ihh2 (Or.inl (R x r₁ r₂ hA)) (Or.inl (R x' r₁ r₂ hB))
        grind[LambdaTerm.Subst,removeNames', Change]
      | inr hB =>
        let ihh1 := ihh1 (Or.inl (L x r₁ r₂ hA)) (Or.inr hB)
        let ihh2 := ihh2 (Or.inl (R x r₁ r₂ hA)) (Or.inr hB)
        grind[LambdaTerm.Subst,removeNames', Change]
    | inr hA =>
      cases B with
      | inl hB =>
        let ihh1 := ihh1 (Or.inr hA) (Or.inl (L x' r₁ r₂ hB))
        let ihh2 := ihh2 (Or.inr hA) (Or.inl (R x' r₁ r₂ hB))
        grind[LambdaTerm.Subst,removeNames', Change]
      | inr hB =>
        let ihh1 := ihh1 (Or.inr hA) (Or.inr hB)
        let ihh2 := ihh2 (Or.inr hA) (Or.inr hB)
        grind[LambdaTerm.Subst,removeNames', Change]
  case abs arg t ihh=>
    intro d levels A B
    let ihh:= ihh (d+1) (levels.insert arg d)
    cases A with
    | inl hA =>
      cases B with
      | inl hB =>
        let P: (x ∉ FV t ∨ ∃ v, (levels.insert arg d) x = some v) := by by_cases h:arg=x <;> simp_all[FV, Ne.symm]
        let Q: (x' ∉ FV t ∨ ∃ v, (levels.insert arg d) x' = some v) := by by_cases h:arg=x' <;> simp_all[FV, Ne.symm]
        have ihh_eq := ihh P Q
        by_cases h₁: arg=x <;> by_cases h₂: arg=x' <;> by_cases h₃: x=x' <;> simp_all
      | inr hB =>
        have P : (x ∉ FV t ∨ ∃ v, levels.insert arg d x = some v) := by by_cases h:arg=x <;> simp_all[FV, Ne.symm]
        have Q: (x' ∉ FV t ∨ ∃ v, (levels.insert arg d) x' = some v) := by by_cases h:arg=x' <;> simp_all[FV, Ne.symm]
        have ihh_eq := ihh P Q
        by_cases h₁: arg=x <;> by_cases h₂: arg=x' <;> by_cases h₃: x=x' <;> simp_all
    | inr hA =>
      have P : ∃ v, (levels.insert arg d) x = some v := by by_cases hxarg : x = arg <;> simp_all
      let ihh := ihh (Or.inr P)
      cases B with
      | inl hB =>
        let P: (x' ∉ FV t ∨ ∃ v, (levels.insert arg d) x' = some v) := by by_cases h:arg=x' <;> simp_all[FV, Ne.symm]
        have ihh_eq := ihh P
        by_cases h₁: arg=x <;> by_cases h₂: arg=x' <;> by_cases h₃: x=x' <;> simp_all
      | inr hB =>
        have Q : ∃ v, (levels.insert arg d) x' = some v := by by_cases hxarg : x' = arg <;> simp_all
        have ihh := ihh (Or.inr Q)
        by_cases h₁ : arg = x
        · subst h₁
          simp_all
        · by_cases h₂ : arg = x'
          · subst h₂
            simp_all
          · simp_all

lemma LevelsUnfree: ∀ t: LambdaTerm, ∀ x: String, ∀ d:ℕ, ∀ levels levels': Env, x ∉ FV t → (levels.erase x) = (levels'.erase x) → removeNames' d levels t = removeNames' d levels' t := by
  intro t x
  induction t
  case var y =>
    intro d levels levels' h_fv h_erase
    by_cases h_yx : y = x
    · subst h_yx
      simp_all [FV]
    · have h_eval : (levels.erase x) y = (levels'.erase x) y := by rw [h_erase]
      simp_all [removeNames', Env.erase, Ne.symm]
  case app t₁ t₂ ih₁ ih₂ =>
    intro d levels levels' h_fv h_erase
    have h_fv₁ : x ∉ FV t₁ := by intro h; apply h_fv; simp_all [FV]
    have h_fv₂ : x ∉ FV t₂ := by intro h; apply h_fv; simp_all [FV]
    simp only [removeNames']
    congr 1
    · exact ih₁ d levels levels' h_fv₁ h_erase
    · exact ih₂ d levels levels' h_fv₂ h_erase
  case abs arg body ih =>
    intro d levels levels' h_fv h_erase
    simp only [removeNames']
    congr 1
    by_cases h_x_arg : x = arg
    · subst h_x_arg
      have h_env : levels.insert x d = levels'.insert x d := by
        funext k
        by_cases h_k : k = x
        · simp_all [Env.insert]
        · have h_eval : (levels.erase x) k = (levels'.erase x) k := by rw [h_erase]
          simp_all [Env.insert, Env.erase]
      rw [h_env]
    · have h_fv_body : x ∉ FV body := by
        intro h
        apply h_fv
        simp_all [FV, Ne.symm]
      have h_erase_insert : (levels.insert arg d).erase x = (levels'.insert arg d).erase x := by
        funext k
        by_cases h_kx : k = x <;> by_cases h_karg : k = arg <;> simp_all [Env.erase, Env.insert]
        have h_eval : (levels.erase x) k = (levels'.erase x) k := by rw [h_erase]
        simp_all [Env.erase]
      exact ih (d + 1) (levels.insert arg d) (levels'.insert arg d) h_fv_body h_erase_insert

lemma Subst_FV_neq : ∀ t' x x', x ∉ FV t' → x' ∉ FV (LambdaTerm.Subst x x' t') := by
  intro t' x x'
  induction t'
  case var z => grind[FV, LambdaTerm.Subst]
  case app t1 t2 ih1 ih2 => grind[FV,LambdaTerm.Subst]
  case abs u body ih => grind[FV,LambdaTerm.Subst]

theorem AlphaConversion' : ∀ t₁ t₂ : LambdaTerm, ∀ d:ℕ, ∀ levels : Env, Alpha t₁ t₂ → removeNames' d levels t₁ = removeNames' d levels t₂ := by
  intro t₁
  induction t₁
  case var x =>
    intro d levels t₂ A
    rcases A
    simp_all
  case app v w ih1 ih2 =>
    intro t₂ d levels A
    rcases A
    rename_i r₁ r₂ a₁ a₂
    have ih1:= ih1 r₁ d levels a₁
    have ih2:= ih2 r₂ d levels a₂
    simp_all
  case abs x t ih =>
    intro t' d levels A
    rcases A
    rename_i x' t' fv a
    simp_all
    have helpA : (x' ∉ FV t' ∨ ∃ v, levels.insert x' d x' = some v) := by simp_all
    cases fv
    · rename_i fv
      have A := ChangeOfChanges t' x x' (d+1) (levels.insert x' d) (Or.inl fv) helpA
      rw[←A]
      have D:(Change x x' (levels.insert x' d)).erase x' = (levels.insert x d).erase x':=by
        funext k
        by_cases h_xx : x = x' <;> by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]
      have C:=LevelsUnfree (LambdaTerm.Subst x x' t') x' (d+1) (Change x x' (levels.insert x' d)) (levels.insert x d) (Subst_FV_neq t' x x' fv) D
      rw[C]
      grind
    · rename_i h_eq
      subst h_eq
      simp_all
      exact ih t' (d+1) (levels.insert x d) a

theorem AlphaConversion : ∀ t₁ t₂ : LambdaTerm, Alpha t₁ t₂ → removeNames t₁ = removeNames t₂ := by
  intro t₁ t₂ A
  rw[removeNames]
  exact AlphaConversion' t₁ t₂ 0 Env.empty A

@[simp]
def ValidEnv (levels : Env) (d : ℕ) : Prop :=
  -- 1. Injectivity
  (∀ x y v, levels x = some v → levels y = some v → x = y) ∧
  -- 2. Freshness
  (∀ x v, levels x = some v → v < d)

lemma Transposition:∀levels:Env, ∀x x': String,∀ d: ℕ, (Change x x' (levels.insert x' d)).erase x' = (levels.insert x d).erase x' := by
  intro levels x x' d
  funext k
  by_cases h_kx : x = x' <;> by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]

theorem AlphaConversion'' : ∀ t₁ t₂ : LambdaTerm, ∀ d:ℕ, ∀ levels : Env, ValidEnv levels d → removeNames' d levels t₁ = removeNames' d levels t₂ → Alpha t₁ t₂ := by
  intro t₁
  induction t₁
  case var x =>
    intro t₂ d levels I R
    cases t₂ with
    | var x' =>
      rcases I with ⟨h_inj, h_fresh⟩
      cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Alpha.var,removeNames', h_inj x x']
    | _ => grind [removeNames']
  case app v w ih1 ih2 =>
    intro t₂ d levels I R
    cases t₂ with
    | app a b =>
      simp only [removeNames'] at R
      injection R with R1 R2
      have ih1_applied := ih1 a d levels I R1
      have ih2_applied := ih2 b d levels I R2
      exact Alpha.app ih1_applied ih2_applied
    | _ => grind [removeNames']
  case abs x t ih =>
    intro t₂ d levels I R
    cases t₂ with
    | abs x' t' =>
      simp only [removeNames'] at R
      injection R with R_inner

      have I_new : ValidEnv (levels.insert x d) (d + 1) := by
        rcases I with ⟨h_inj, h_fresh⟩
        constructor
        ·
          intro y y' v hy hy'
          simp only [Env.insert] at hy hy'
          by_cases h1 : y = x <;> by_cases h2 : y' = x <;> grind
        ·
          intro y v hy
          simp only [Env.insert] at hy
          by_cases h1 : y = x <;> grind

      have ih := ih (t'.Subst x x') (d+1) (levels.insert x d) I_new
      rw[R_inner] at ih

      -- ???
      have h_not_free : x ∉ FV t' := by sorry

      have h_bridge : removeNames' (d + 1) (levels.insert x' d) t' = removeNames' (d + 1) (levels.insert x d) (t'.Subst x x') := by
        have helpA : (x' ∉ FV t' ∨ ∃ v, (levels.insert x' d) x' = some v) := Or.inr ⟨d, by simp [Env.insert]⟩
        have A_eq := ChangeOfChanges t' x x' (d+1) (levels.insert x' d) (Or.inl h_not_free) helpA
        rw [←A_eq]
        have D:= Transposition levels x x' d
        have C := LevelsUnfree (LambdaTerm.Subst x x' t') x' (d+1) (Change x x' (levels.insert x' d)) (levels.insert x d) (Subst_FV_neq t' x x' h_not_free) D
        rw [C]
      grind[Alpha]
    | _ => grind [removeNames']
