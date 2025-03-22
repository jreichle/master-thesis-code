import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx


theorem boundary_helper_sigma_elim :
    C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌈(ₛidₚ), a, b⌉ = C⌈a&b⌉₀ :=
  by
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
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        rfl

-- theorem boundary_helper_sigma_elim_weak {n : Nat} {C : Tm (n + 1)}:
--     C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = C⌈(ₛidₚ), v(1)&v(0)⌉⌊↑ₚ↑ₚidₚ⌋ :=
--   by
--     simp [substitution_comp_ρσ]
--     simp [comp_weaken_substitute]
--     simp [comp_weaken]
--     simp [weaken]

theorem test_this_lol {n : Nat} {t : Tm (n + 2)} {σ : Subst n (n + 2)} {s : Tm (n + 1)} {u : Tm (n)}:
    t⌈s⌉₀⌈u⌉₀ = t⌈(ₛidₚ), u, (s⌈(ₛidₚ), u⌉)⌉ :=
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
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        rfl

theorem boundary_helper_iden_elim_one {n : Nat} {t : Tm (n + 3)} {r : Tm (n + 2)} {s : Tm (n + 1)} {u : Tm (n)}:
    t⌈r⌉₀⌈s⌉₀⌈u⌉₀ = t⌈(ₛidₚ), u, (s⌈(ₛidₚ), u⌉), (r⌈(ₛidₚ), s⌉⌈(ₛidₚ), u⌉)⌉ :=
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
        rw [substitution_comp]
        simp [comp_substitute_substitute]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        cases i' with
        | zero =>
          simp [substitute]
          simp [comp_substitute_weaken]
          simp [comp_substitute_substitute]
          simp [substitute_var]
          rfl
        | succ j =>
          simp [substitute]
          simp [comp_substitute_weaken]
          simp [comp_substitute_substitute]
          simp [substitute_var]
          rfl

theorem old_test_hahah :
    B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉⌈a⌉₀
    = B⌈(ₛidₚ), a, a, A.refl a⌉ :=
  by
    simp [substitute_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [substitute]
    simp [substitute_var]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        simp [weakening_id]
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [weakening_id]
        rfl

theorem vone_to_vtwo :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌈(ₛ↑ₚidₚ), (v(0)⌊↑ₚidₚ⌋)⌉
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(1) :=
  by
    simp [substitute]
    simp [substitute_var]
    simp [weaken]
    simp [weaken_var]
    simp [substitution_comp_σρ]
    simp [comp_substitute_weaken]
    simp [comp_weaken]
    apply And.intro
    · apply conversion_sub_weak
    · aesop

theorem separate_two_sub :
    B⌈(.refl (A⌊↑ₚidₚ⌋) v(0))⌊↑ₚidₚ⌋⌉₀⌈v(0)⌉₀ = B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉ :=
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
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        rfl

theorem clean_this_mess_too :
    A⌈⇑ₛ⇑ₛ((ₛidₚ), a)⌉⌈⇑ₛ((ₛidₚ), a')⌉⌈p⌉₀
    = A⌈(ₛidₚ), a, a', p⌉ :=
  by
    simp [substitute_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [substitution_id]
        simp [weakening_id]
        simp [←substitution_conv_var]
        simp [comp_substitute_substitute]
        simp [comp_substitute_weaken]
        simp [substitution_id]

theorem clean_this_mess_asap :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌈⇑ₛ((ₛidₚ), a)⌉⌈a'⌉₀
    = (a ≃[A] a') :=
  by
    simp [substitute_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    simp [substitution_id]
    simp [substitute]
    repeat' apply And.intro
    · simp [substitution_comp_σρ]
      simp [comp_substitute_weaken]
      simp [substitution_id]
    · simp [substitute_var]
      rfl
    · simp [substitute_var]
      rfl

theorem even_new_test {B : Tm (n + 3)} :
    B⌈⇑ₛ((v(1) : Tm (n + 2))↑/ₙ(Nat.le_refl (n + 2)))⌉⌈A⌊↑ₚ↑ₚidₚ⌋.refl v(1)⌉₀⌈v(0)⌉₀
    = B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉ :=
  by
    simp [substitute_zero]
    simp [substitution_comp]
    simp [n_substitution_shift]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    simp [comp_weaken]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        simp [weakening_id]
        rw (config := {occs := .pos [1]}) [←weakening_shift_id]
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [weaken]
        simp [weaken_var]
        simp [comp_substitute_substitute]
        simp [←substitution_conv_var]
        cases i' with
        | zero =>
          simp [substitute]
          rfl
        | succ j =>
          simp [substitute]
          rfl

theorem new_test_hahaha :
    B⌈(.refl A a)⌊↑ₚ↑ₚidₚ⌋⌉₀⌈a⌊↑ₚidₚ⌋⌉₀⌈a⌉₀ = B⌈(ₛidₚ), a, a, .refl A a⌉ :=
  by
    simp [substitute_zero]
    rw (config := {occs := .pos [2]}) [←weakening_shift_id]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    simp [substitution_comp]
    simp [substitution_comp_σρ]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    simp [substitute]
    simp [←substitution_refl]
    simp [substitution_id]
    simp [substitution_conv_zero]
    simp [substitution_shift_substitute_zero]

theorem boundary_helper_nat {n : Nat} {t : Tm (n + 1)}:
    t⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉ = t⌊⇑ₚ↑ₚidₚ⌋⌈((ₛidₚ), 𝓈(v(0)))⌉:=
  by
    rw [substitution_comp_σρ]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        rw [←substitution_comp_σρ]
        simp [weaken]
        simp [weaken_var]
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        rw [←substitution_comp_σρ]
        simp [substitute]
        simp [substitute_var]
        simp [weaken]
        simp [weaken_var]
        rfl

theorem insane {x : Tm n}:
    A⌈𝓈(x)⌉₀⌊↑ₚidₚ⌋ = A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌈⇑ₛ((ₛidₚ), x)⌉ :=
  by
    simp [substitute_zero]
    simp [substitution_comp_ρσ]
    simp [substitution_comp]
    simp [comp_weaken_substitute]
    simp [comp_substitute_substitute]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        simp [weakening_id]
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [weakening_id]
        simp [substitute]
        simp [substitute_var]
        rfl

theorem test_insanity {A : Tm (n + 1)}:
    A⌈(ₛidₚ), x⌉⌊↑ₚidₚ⌋ = A⌈ₛidₚ⌉ :=
  by
    simp [substitution_comp_ρσ]
    simp [comp_weaken_substitute]
    simp [weakening_id]
    apply substitution_var_substitute
    intro x
    cases x
    case a.mk i hFin =>
      cases i with
      | zero =>
        simp [substitute]
        simp [substitute_var]
        sorry
      | succ i' =>
        sorry

theorem lol111 :
    A⌈𝓈(x)⌉₀ = A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌈((ₛidₚ), x)⌉ :=
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
        simp [weakening_id]
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        rfl

-- theorem lol1111 :
--     A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉ = A⌈(ₛ↑ₚidₚ), v(0)⌉⌈𝓈(v(0))⌉₀ :=
--   by
--     simp [substitute_zero]
--     simp [substitution_comp_ρσ]
--     simp [substitution_comp]
--     simp [comp_weaken_substitute]
--     simp [comp_substitute_substitute]
--     apply substitution_var_substitute
--     intro x
--     cases x
--     case a.mk i hFin =>
--       cases i with
--       | zero =>
--         simp [weakening_id]
--         simp [substitute]
--         simp [substitute_var]
--         simp [comp_weaken_substitute]
--         simp [substitute_var]
--         simp [weaken]
--         simp [weaken_var]
--         sorry
--       | succ i' =>
--         simp [substitute]
--         simp [substitute_var]
--         sorry
