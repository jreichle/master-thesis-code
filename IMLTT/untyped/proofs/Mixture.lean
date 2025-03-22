import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Conversion
import IMLTT.untyped.proofs.Composition

theorem weak_sub_lift_weak_before_subst :
    G⌊⇑ₚ(ρ ₚ∘ₚρ')⌋⌈a⌉ = G⌊⇑ₚρ'⌋⌊⇑ₚρ⌋⌈a⌉ :=
  by
    simp [weakening_comp]
    simp [comp_weaken]

theorem weak_sub_zero :
    t⌈a⌉₀⌊ρ⌋ = t⌊⇑ₚρ⌋⌈a⌊ρ⌋⌉₀ :=
  by
    simp [←substitution_conv_zero]
    rw [substitution_comp_ρσ]
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [weakening_lift_id]
      simp [weakening_id]
    | shift ρ' =>
      rw [substitution_comp_σρ]
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]
      apply substitution_var_substitute
      intro x
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          simp [shift_tm]
          rw [←weakening_shift_id]
          rw (config := {occs := .pos [2]}) [←weakening_shift_id]
          simp [weakening_id]
          rfl
        | succ i' =>
          simp [substitute]
          simp [substitute_var]
          simp [shift_tm]
          simp [←substitution_conv_var]
          simp [←substitution_comp_ρσ]
          simp [substitution_id]
          rw [weakening_shift_id]
    | lift ρ' =>
      rw [substitution_comp_σρ]
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]

-- FIXME: better names
theorem weak_sub_shift :
    t⌈(ₛ↑ₚidₚ), a⌉⌊⇑ₚρ⌋ = t⌊⇑ₚρ⌋⌈(ₛ↑ₚidₚ), (a⌊⇑ₚρ⌋)⌉ :=
  by
    simp [substitution_comp_ρσ]
    simp [substitution_comp_σρ]
    simp [comp_substitute_weaken]
    simp [comp_weaken_substitute]
    simp [comp_weaken]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        rw [←weakening_shift_id]
        simp [←weakening_comp]
        simp [weakening_id]
        simp [←substitution_comp_σρ]
        rfl

-- TODO: if nat added
-- wk-β-natrec : ∀ (ρ : Wk m n )G
--   → Π ℕ ▹ (Π wk (lift ρ) G ▹ wk (lift (lift ρ)) (wk1 (G [ suc (var x0) ]↑)))
--   ≡ Π ℕ ▹ (wk (lift ρ) G ▹▹ wk (lift ρ) G [ suc (var x0) ]↑)

theorem substitution_var_single_comp :
    v(x)⌈(ₛidₚ), a ₛ∘ₛ⇑ₛσ⌉ = v(x)⌈σ, a⌉ :=
  by
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        simp [←substitution_comp]
        simp [substitution_id]

theorem substitution_single_comp : -- XXX:
    t⌈(ₛidₚ), a ₛ∘ₛ⇑ₛσ⌉ = t⌈σ, a⌉ :=
  by
    apply substitution_var_substitute
    apply substitution_var_single_comp

theorem substitution_comp_id :
    t⌈(ₛidₚ)ₛ∘ₛσ⌉ = t⌈σ⌉ :=
  by
    simp [←substitution_comp]
    simp [substitution_id]

theorem substitution_extend :
    t⌈⇑ₛσ⌉⌈a⌉₀ = t⌈σ, a⌉ :=
  by
    simp [←substitution_conv_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        simp [substitution_comp_id]

theorem substitution_extend_lift :
    t⌈⇑ₛσ⌉⌊⇑ₚρ⌋⌈a⌉₀ = t⌈ρ ₚ∘ₛσ, a⌉ :=
  by
    simp [substitution_comp_ρσ]
    simp [comp_weaken_substitute]
    simp [substitution_extend]

theorem substitution_zero_lift : 
    t⌈a⌉₀⌈σ⌉ = t⌈⇑ₛσ⌉⌈a⌈σ⌉⌉₀ :=
  by
    simp [←substitution_conv_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        simp [substitution_comp_id]

theorem idWkLiftSubstLemma :
    t⌈⇑ₛσ⌉⌊⇑ₚ↑ₚidₚ⌋⌈v(0)⌉₀ = t⌈⇑ₛσ⌉ :=
  by
    simp [substitution_extend_lift]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [shift_tm]
        simp [←substitution_conv_var]
        simp [substitution_comp_ρσ]

theorem substVarCompTest :
    v(x)⌈(ₛ↑ₚidₚ), (t⌈⇑ₛσ⌉)ₛ∘ₛ⇑ₛσ⌉ = v(x)⌈⇑ₛσ ₛ∘ₛ((ₛ↑ₚidₚ), t)⌉ :=
  by
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [comp_substitute_substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [comp_substitute_substitute]
        simp [substitute_var]
        simp [comp_substitute_weaken]
        simp [←substitution_conv_var]
        simp [←substitution_comp]
        simp [←substitution_conv_shift_id]
        simp [←conversion_sub_weak]

theorem singleSubstLift :
    t⌈(ₛ↑ₚidₚ), a⌉⌈⇑ₛσ⌉ = t⌈⇑ₛσ⌉⌈(ₛ↑ₚidₚ), (a⌈⇑ₛσ⌉)⌉ :=
  by
    simp [substitution_comp]
    apply substitution_var_substitute
    intro x
    simp [←substVarCompTest]

-- own
theorem lift_single_subst_tt :
   A⌊⇑ₚweaken_from n l⌋⌈⋆⌉₀ = A⌈⋆⌉₀⌊weaken_from n l⌋ :=
  by
    simp [←substitution_conv_zero]
    simp [substitution_comp_σρ]
    simp [comp_substitute_weaken]
    simp [substitution_comp_ρσ]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [←substitution_comp_ρσ]
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [←substitution_comp_ρσ]
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        rw [←substitution_comp_σρ]
        simp [substitution_id]
        simp [weakening_id]

theorem substitution_shift_substitute_zero :
    A⌊↑ₚidₚ⌋⌈s⌉₀ = A :=
  by
    simp [substitute_zero]
    simp [substitution_comp_σρ]
    simp [comp_substitute_weaken]
    simp [substitution_id]

theorem conversion_var_lift_n_sub_weak :
    v(x)⌈lift_subst_n n (ₛρ)⌉ = v(x)⌊lift_weak_n n ρ⌋ :=
  by
    induction n with
    | zero =>
      simp [lift_weak_n]
      simp [lift_subst_n]
      apply conversion_sub_weak
    | succ n' ih =>
      simp [lift_weak_n]
      simp [lift_subst_n]
      cases x
      case mk i hFin =>
        cases i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          simp [weaken]
          simp [weaken_var]
          rfl
        | succ i' =>
          simp [substitute]
          simp [substitute_var]
          simp [←substitution_conv_var]
          rw [ih]
          simp [shift_tm]
          rw [weakening_shift_id]
          simp [weaken]
          simp [weaken_var]


theorem substitution_twice_zero {n : Nat} {T : Tm (n + 2)} {b : Tm (n)} {a : Tm (n)} :
    T⌈(ₛidₚ), a, b⌉ = T⌈b⌊↑ₚidₚ⌋⌉₀⌈a⌉₀ :=
  by
    simp [substitute_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        simp [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        simp [substitution_id]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        rfl


theorem substitution_separate {n m : Nat} {t : Tm (n + 1)} {s : Tm m} {σ : Subst m n} :
    t⌈σ, s⌉ = t⌈⇑ₛσ⌉⌈s⌉₀ :=
  by
    rw [substitute_zero]
    rw [substitution_comp]
    simp [comp_substitute_substitute]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        rw [substitute]
        rw [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        rw [←substitution_comp]
        simp [substitution_id]



