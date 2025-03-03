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
      | succ i' =>
        simp [substitute]
        simp [substitute_var]


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

theorem new_test_hahaha :
    B⌈(.refl A a)⌊↑ₚ↑ₚidₚ⌋⌉₀⌈a⌊↑ₚidₚ⌋⌉₀⌈a⌉₀ = B⌈(ₛidₚ), a, a, .refl A a⌉ :=
  by
    simp [substitute_zero]
    rw (config := {occs := .pos [2]}) [←weakening_shift_id]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    simp [substitute]
    simp [←substitution_refl]
    simp [←weakening_refl]
    simp [substitution_conv_zero]
    simp [substitution_shift_substitute_zero]
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
        simp [comp_substitute_substitute]
        simp [comp_substitute_weaken]
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        rfl

-- theorem boundary_helper_iden_elim_two  {n : Nat} {t : Tm (n + 3)} {r : Tm (n + 2)} {s : Tm (n + 1)} {u : Tm (n)} :
--     t⌈(ₛidₚ), u, s, r⌉ = t⌈(ₛidₚ), u, (s⌈(ₛidₚ), u⌉), (r⌈(ₛidₚ), s⌉⌈(ₛidₚ), u⌉)⌉ :=
--   by
--     sorry
