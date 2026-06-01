import TAPLFormalization.«02.5-alpha_reduction».AST

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

lemma ChangeOfChanges : ∀t : LambdaTerm, ∀ x x' : String, ∀ d: Nat, ∀ levels: Env, (x∉ FV t) ∨ (∃ v, levels x = some v) →  (x'∉ FV t) ∨  (∃ v, levels x' = some v) → removeNames' d (Change x x' levels) (t.Subst x x') = removeNames' d levels t := by
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

@[simp]
def ValidEnv (levels : Env) (d : ℕ) : Prop :=
  -- 1. Injectivity
  (∀ x y v, levels x = some v → levels y = some v → x = y) ∧
  -- 2. Freshness
  (∀ x v, levels x = some v → v < d)

lemma PreservationValid (levels: Env) (d:ℕ) (x:String): ValidEnv levels d → ValidEnv (levels.insert x d) (d+1):= by
  grind[ValidEnv, Env.insert]

lemma Transposition:∀levels:Env, ∀x x': String,∀ d: ℕ, (Change x x' (levels.insert x' d)).erase x' = (levels.insert x d).erase x' := by
  intro levels x x' d
  funext k
  by_cases h_kx : x = x' <;> by_cases h_kx : k = x <;> by_cases h_kx' : k = x' <;> cases hx : levels x <;> cases hx' : levels x' <;> simp_all [Change, Ne.symm]




abbrev LinkedState := LambdaTerm × LambdaTerm × Env × Env × ℕ

inductive Step : LinkedState → LinkedState → Prop where
  | abs_step (arg₁ arg₂ : String) (body₁ body₂ : LambdaTerm) (level₁ level₂ : Env) (d : ℕ) :
      Step (.abs arg₁ body₁, .abs arg₂ body₂, level₁, level₂, d) (body₁,body₂, level₁.insert arg₁ d, level₂.insert arg₂ d, d+1)
  | app_left (t₁₂ t₁₁ t₂₁ t₂₂ : LambdaTerm) (level₁ level₂ : Env) (d : ℕ) :
      Step (.app t₁₁ t₁₂,.app t₂₁ t₂₂, level₁, level₂, d) (t₁₁,t₂₁, level₁, level₂, d)
  | app_right (t₁₂ t₁₁ t₂₁ t₂₂ : LambdaTerm) (level₁ level₂ : Env) (d : ℕ) :
      Step (.app t₁₁ t₁₂,.app t₂₁ t₂₂, level₁, level₂, d) (t₁₂,t₂₂, level₁, level₂, d)

inductive RealPath : List LinkedState → Prop where
  | singleton (x₁ x₂: String) (level₁ level₂: Env) (d:Nat) : RealPath [(.var x₁, .var x₂, level₁, level₂, d)]
  | cons (s₁ s₂ : LinkedState) (rest : List LinkedState)
      (hStep : Step s₁ s₂)
      (hRest : RealPath (s₂ :: rest)) : RealPath (s₁ :: s₂ :: rest)

@[simp]
def avoidsAbsX (x : String) : List LinkedState → Prop
  | [] => True
  | (t, _, _, _, _) :: rest => (∀ body, t ≠ .abs x body) ∧ avoidsAbsX x rest

lemma free_implies_path (t₁ : LambdaTerm) (x : String) : ∀ t₂ level₁ level₂ d, removeNames' d level₁ t₁ = removeNames' d level₂ t₂ →
    x ∈ FV t₁ →
      ∃ (path : List LinkedState),
        path.head? = some (t₁, t₂, level₁, level₂, d) ∧
        RealPath path ∧
        avoidsAbsX x path ∧
        ∃ a b c d, path.getLast? = some (.var x, a, b, c, d):= by
  induction t₁ with
  | var name =>
    intro t₂ level₁ level₂ d rh h
    use [(.var x, t₂, level₁, level₂, d)]
    simp_all[FV]
    have ⟨y, m⟩: ∃ y, t₂ = .var y := by
      cases t₂ with
      | var y =>
        exact ⟨y, rfl⟩
      | abs arg body =>
        revert rh
        cases level₁ name <;> intro rh <;> contradiction
      | app l r =>
        revert rh
        cases level₁ name <;> intro rh <;> contradiction
    rw[m]
    constructor
  | abs arg body ih =>
    intro t₂ level₁ level₂ d rh h
    simp[FV, Finset.mem_erase] at h
    rcases h with ⟨h_neq, h_body⟩
    simp_all
    cases t₂ <;> try grind[removeNames']
    rename_i arg₂ body₂
    have:removeNames' (d + 1) (level₁.insert arg d) body = removeNames' (d + 1) (level₂.insert arg₂ d) body₂:= by
      simp_all[removeNames']
    have ⟨path, hHead, hPath, hAvoids, hTail⟩:= ih body₂ (level₁.insert arg d) (level₂.insert arg₂ d) (d+1) this
    cases path with
    | nil => simp at hHead
    | cons s rest =>
      use (.abs arg body, .abs arg₂ body₂, level₁, level₂, d) :: (body, body₂, level₁.insert arg d, level₂.insert arg₂ d, d + 1) :: rest
      simp_all
      constructor
      constructor
      constructor
      exact hPath
      grind
  | app t₁ t₂ ih₁ ih₂ =>
    intro t₂ level₁ level₂ d rh h
    cases t₂ <;> try grind[removeNames']
    simp only [FV, Finset.mem_union] at h
    rename_i t₂₁ t₂₂
    cases h with
    | inl h₁ =>
      simp_all
      have :  removeNames' d level₁ t₁ = removeNames' d level₂ t₂₁ := by grind
      have ⟨path, hHead, hPath, hAvoids, hTail⟩ := ih₁ t₂₁ level₁ level₂ d this
      cases path with
      | nil => simp at hHead
      | cons s rest =>
        use (.app t₁ t₂, .app t₂₁ t₂₂, level₁, level₂, d) :: (t₁, t₂₁, level₁, level₂, d) :: rest
        simp_all
        constructor
        constructor
        exact hPath
    | inr h₂ =>
      simp_all
      have :  removeNames' d level₁ t₂ = removeNames' d level₂ t₂₂ := by grind
      have ⟨path, hHead, hPath, hAvoids, hTail⟩ := ih₂ t₂₂ level₁ level₂ d this
      cases path with
      | nil => simp at hHead
      | cons s rest =>
        use (.app t₁ t₂, .app t₂₁ t₂₂, level₁, level₂, d) :: (t₂, t₂₂, level₁, level₂, d) :: rest
        simp_all
        constructor
        constructor
        exact hPath

abbrev Invariant (x : String) (state : LinkedState) : Prop :=
  let (t₁, t₂, level₁, level₂, d) := state
  level₁ x ≠ level₂ x ∧
  (∀ y v, level₁ x = some v → level₂ y = some v → x = y) ∧
  ValidEnv level₁ d ∧
  ValidEnv level₂ d ∧
  removeNames' d level₁ t₁ = removeNames' d level₂ t₂

lemma InvariantIsPathInvariant (x : String) :
    ∀ (path : List LinkedState) (s_start s_end : LinkedState),
      RealPath path →
      avoidsAbsX x path →
      path.head? = some s_start →
      path.getLast? = some s_end →
      Invariant x s_start →
      Invariant x s_end := by
  intro path
  induction path
  · grind
  · rename_i head tail ih
    intro start_ end_ rh ah h₁ h₂ inh
    cases tail with
    | nil => grind
    | cons s rest =>
      have rh': RealPath (s :: rest) := by grind[RealPath]
      have ah': avoidsAbsX x (s :: rest):= by grind[avoidsAbsX]
      have hh': (s :: rest).head? = some s := by grind
      have he': (s :: rest).getLast? = some end_:=by grind
      have := ih s end_ rh' ah' hh' he'
      apply this
      rw[Invariant]
      have step: Step head s := by
        cases rh with
        | cons _ _ _ hStep hRest =>
          exact hStep
      have: head=start_:=by grind
      subst this
      clear rh' ah' hh' he' ih h₂ this h₁ end_
      have ⟨t₁₁, t₁₂, level₁₁, level₁₂, d₁⟩:=head
      have ⟨t₂₁, t₂₂, level₂₁, level₂₂, d₂⟩:=s
      have ⟨A,B,C,D,E⟩ := inh
      dsimp only
      cases step
      · rename_i arg₁ arg₂
        grind[avoidsAbsX,ValidEnv, Env.insert,removeNames']
      · rename_i r₁ r₂
        grind[removeNames']
      · rename_i r₁ r₂
        grind[removeNames']


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
        · intro y y' v hy hy'
          simp only [Env.insert] at hy hy'
          by_cases h1 : y = x <;> by_cases h2 : y' = x <;> grind
        · intro y v hy
          simp only [Env.insert] at hy
          by_cases h1 : y = x <;> grind

      have ih := ih (t'.Subst x x') (d+1) (levels.insert x d) I_new
      rw[R_inner] at ih

      by_cases h:x=x'
      · constructor
        · exact Or.inr h
        · apply ih
          rw[h, SubstIsSane]
      · have h_not_free : x ∉ FV t' := by
          intro contr
          have:removeNames' (d + 1) (levels.insert x' d) t'=removeNames' (d + 1) (levels.insert x d) t:= by grind
          have ⟨path, bh, rh, ah, eh⟩:=free_implies_path t' x t (levels.insert x' d) (levels.insert x d) (d+1) this contr
          have ⟨a',b',c',d',eh⟩ := eh
          have inv : Invariant x (t', t, (levels.insert x' d), (levels.insert x d), (d+1)) := by
            grind[ValidEnv, Env.insert]
          have ⟨i₁, i₂, i₃, i₄, i₅⟩:=InvariantIsPathInvariant x path (t', t, (levels.insert x' d), (levels.insert x d), (d+1)) (LambdaTerm.var x, a', b', c', d') rh ah bh eh inv
          cases a' <;> try grind[removeNames']

        have h_bridge : removeNames' (d + 1) (levels.insert x' d) t' = removeNames' (d + 1) (levels.insert x d) (t'.Subst x x') := by
          have helpA : (x' ∉ FV t' ∨ ∃ v, (levels.insert x' d) x' = some v) := Or.inr ⟨d, by simp [Env.insert]⟩
          have A_eq := ChangeOfChanges t' x x' (d+1) (levels.insert x' d) (Or.inl h_not_free) helpA
          rw [←A_eq]
          have D:= Transposition levels x x' d
          have C := LevelsUnfree (LambdaTerm.Subst x x' t') x' (d+1) (Change x x' (levels.insert x' d)) (levels.insert x d) (Subst_FV_neq t' x x' h_not_free) D
          rw [C]
        grind[Alpha]


    | _ => grind [removeNames']

theorem AlphaConversion : ∀ t₁ t₂ : LambdaTerm, Alpha t₁ t₂ ↔ removeNames t₁ = removeNames t₂ := by
  intro t₁ t₂
  constructor
  · intro A
    rw[removeNames]
    exact AlphaConversion' t₁ t₂ 0 Env.empty A
  · intro A
    have EmptyIsValid : ValidEnv Env.empty 0 := by simp_all
    exact AlphaConversion'' t₁ t₂ 0 Env.empty EmptyIsValid A
