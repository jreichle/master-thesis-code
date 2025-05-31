import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Macros
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Conversion
import IMLTT.untyped.proofs.Composition

theorem shift_weaken_from {hl : l ≤ n} :
    A⌊↑ₚidₚ⌋⌊weaken_from (n + 1) l⌋ = A⌊weaken_from n l⌋⌊↑ₚidₚ⌋ :=
  by
    substitution_norm

theorem substitution_zero_weak :
    t⌈a⌉₀⌊ρ⌋ = t⌊⇑ₚρ⌋⌈a⌊ρ⌋⌉₀ :=
  by
    substitution_norm

theorem substitution_zero_shift :
    t⌈(ₛidₚ)⋄ a⌉⌊↑ₚidₚ⌋ = t⌊↑ₚidₚ⌋⌈⇑ₛ((ₛidₚ)⋄ a)⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_zero_weak_simp :
    t⌊⇑ₚρ⌋⌈(ₛidₚ)⋄ (a⌊ρ⌋)⌉ = t⌈(ₛidₚ)⋄ a⌉⌊ρ⌋ :=
  by
    substitution_norm

@[simp]
theorem substitution_lift_weak_subst :
    t⌊⇑ₚρ⌋⌈(ₛ↑ₚidₚ)⋄ (a⌊⇑ₚρ⌋)⌉ = t⌈(ₛ↑ₚidₚ)⋄ a⌉⌊⇑ₚρ⌋ :=
  by
    substitution_norm

@[simp]
theorem substitution_var_single_comp :
    v(x)⌈(ₛidₚ)⋄ a ₛ∘ₛ⇑ₛσ⌉ = v(x)⌈σ⋄ a⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_single_comp :
    t⌈(ₛidₚ)⋄ a ₛ∘ₛ⇑ₛσ⌉ = t⌈σ⋄ a⌉ :=
  by
    substitution_norm

@[simp]
theorem weakening_var_comp_id :
    x⌊ρ ₚ∘ₚidₚ⌋ᵥ = x⌊ρ⌋ᵥ :=
  by
    simp [←weakening_var_comp]

@[simp]
theorem weakening_comp_id :
    t⌊ρ ₚ∘ₚidₚ⌋ = t⌊ρ⌋ :=
  by
    simp [←weakening_comp]

@[simp]
theorem substitution_var_comp_id :
    x⌈(ₛidₚ)ₛ∘ₛσ⌉ᵥ = x⌈σ⌉ᵥ :=
  by
    simp [←substitution_var_comp]

@[simp]
theorem substitution_comp_id :
    t⌈(ₛidₚ)ₛ∘ₛσ⌉ = t⌈σ⌉ :=
  by
    simp [←substitution_comp]

@[simp]
theorem substitution_var_comp_σρ_id :
    x⌈(ₛidₚ) ₛ∘ₚρ⌉ᵥ = x⌊ρ⌋ᵥ :=
  by
    simp [←substitution_var_comp_σρ]

@[simp]
theorem substitution_comp_σρ_id :
    t⌈(ₛidₚ) ₛ∘ₚρ⌉ = t⌊ρ⌋ :=
  by
    simp [←substitution_comp_σρ]

@[simp]
theorem substitution_var_comp_ρσ_id :
    x⌈ρ ₚ∘ₛ(ₛidₚ)⌉ᵥ = x⌊ρ⌋ᵥ :=
  by
    simp [←substitution_var_comp_ρσ]

@[simp]
theorem substitution_comp_ρσ_id :
    t⌈ρ ₚ∘ₛ(ₛidₚ)⌉ = t⌊ρ⌋ :=
  by
    simp [←substitution_comp_ρσ]

@[simp]
theorem substitution_extend :
    t⌈⇑ₛσ⌉⌈a⌉₀ = t⌈σ⋄ a⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_extend_lift :
    t⌈⇑ₛσ⌉⌊⇑ₚρ⌋⌈(ₛidₚ)⋄ a⌉ = t⌈ρ ₚ∘ₛσ⋄ a⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_zero_lift_simp :
    t⌈⇑ₛσ⌉⌈(ₛidₚ)⋄ (a⌈σ⌉)⌉ = t⌈(ₛidₚ)⋄ a⌉⌈σ⌉ :=
  by
    substitution_norm

theorem substitution_zero_lift :
    t⌈a⌉₀⌈σ⌉ = t⌈⇑ₛσ⌉⌈a⌈σ⌉⌉₀ :=
  by
    substitution_norm

@[simp]
theorem substitution_shift_lift_zero :
    t⌈⇑ₛσ⌉⌊⇑ₚ↑ₚidₚ⌋⌈(ₛidₚ)⋄ v(0)⌉ = t⌈⇑ₛσ⌉ :=
  by
    substitution_norm

theorem substitution_shift_substitute_zero :
    A⌊↑ₚidₚ⌋⌈s⌉₀ = A :=
  by
    substitution_norm

@[simp]
theorem substitution_shift_substitute_zero_simp :
    A⌊↑ₚidₚ⌋⌈(ₛidₚ)⋄ s⌉ = A :=
  by
    substitution_norm

@[simp]
theorem substitution_separate {n m : Nat} {t : Tm (n + 1)} {s : Tm m} {σ : Subst m n} :
    t⌈⇑ₛσ⌉⌈(ₛidₚ)⋄ s⌉ = t⌈σ⋄ s⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_weak_id_shift :
    B⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)⌉ = B⌊↑ₚidₚ⌋ :=
  by
    substitution_norm

theorem substitution_nat_succ_apart :
    t⌈(ₛidₚ)⋄ 𝓈(a)⌉ = t⌈(ₛ↑ₚidₚ)⋄  𝓈(v(0))⌉⌈(ₛidₚ)⋄ a⌉ :=
  by
    substitution_norm

theorem weak_substitution_eq_weakening_substitution {l m : Nat} {leq : (l + 1) ≤ m} {S : Tm m} {s : Tm (l + 1)}:
    S⌊↑₁m↬l⌋⌈s/ₙ(leq)⌉ = S⌈s↑/ₙ(leq)⌉ :=
  by
    induction m with
    | zero =>
      substitution_step
    | succ m' ih =>
      any_goals substitution_norm
      · cases m' with
        | zero =>
          substitution_step
        | succ n =>
          unfold n_substitution
          split
          case isTrue =>
            substitution_step
          case isFalse =>
            unfold n_substitution_shift
            split
            any_goals substitution_norm
      · cases m' with
        | zero =>
          substitution_step
        | succ n =>
          unfold n_substitution
          split
          case isTrue =>
            substitution_step
            simp only [←substitution_conv_var]
            rw [←ih]
            substitution_step
          case isFalse =>
            unfold n_substitution_shift
            any_goals substitution_norm

theorem weak_substitution_eq_weakening_substitution_gen_context {l n : Nat} {s : Tm (l + 1)} {Δ : CtxGen (l + 1) n} :
    ⌈s⌉(⌊↑₁↬l⌋Δ w/(Nat.le_refl (l + 1))) = ⌈s↑⌉(Δ w/(Nat.le_refl (l + 1))) :=
  by
    induction Δ with
    | start =>
      substitution_norm
    | expand Δ' S' ih =>
      simp [weaken_from_into_gen_ctx]
      simp [substitute_into_gen_ctx]
      simp [substitute_shift_into_gen_ctx]
      apply And.intro
      · apply ih
      · apply weak_substitution_eq_weakening_substitution
