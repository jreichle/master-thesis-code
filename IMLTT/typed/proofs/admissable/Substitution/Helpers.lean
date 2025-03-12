import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.WeakeningGeneral

import Mathlib.Tactic.ExtractGoal

theorem subst_subst_sigma_c :
    c⌈(ₛidₚ), a, b⌉⌈σ⌉
    = c⌈lift_subst_n 2 σ⌉⌈(ₛidₚ), (a⌈σ⌉), (b⌈σ⌉)⌉ :=
  by
    simp [substitution_comp]
    apply substitution_var_substitute
    simp [lift_subst_n]
    simp [comp_substitute_substitute]
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [substitute_var]
        rfl
      | succ i' =>
        simp [substitute]
        simp [substitute_var]
        simp [←substitution_conv_var]
        simp [←substitution_comp]
        simp [←substitution_comp_σρ]
        simp [substitution_id]
        simp [weakening_id]

theorem subst_subst_sigma_C :
    C⌈⇑ₛσ⌉⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ =
    C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌈⇑ₛ⇑ₛσ⌉ :=
  by
    simp [substitution_comp]
    apply substitution_var_substitute
    intro x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [substitute_var]
        aesop
      | succ i' =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [substitute_var]
        simp [shift_tm]
        simp [←substitution_conv_var]
        rw [←substitution_comp]
        rw [←substitution_comp_σρ]
        rw [←weakening_shift_id]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        simp [weakening_id]
        rw (config := {occs := .pos [1]}) [weakening_shift_id]
        simp [←conversion_sub_weak]

theorem subst_subst_iden_elim :
    B⌈(ₛidₚ), a, b, c⌉⌈σ⌉
    = B⌈lift_subst_n 3 σ⌉⌈(ₛidₚ), (a⌈σ⌉), (b⌈σ⌉), (c⌈σ⌉)⌉ :=
  by
    simp [substitution_comp]
    simp [lift_subst_n]
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
        cases i' with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          rfl
        | succ j =>
          cases j with
          | zero =>
            simp [substitute]
            simp [substitute_var]
          | succ j' =>
            simp [substitute]
            simp [substitute_var]
            simp [←substitution_conv_var]
            simp [←substitution_comp]
            simp [←substitution_comp_σρ]
            simp [weakening_id]
            simp [substitution_id]

theorem helper_subst_iden_propagate_subst :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌈⇑ₛ⇑ₛσ⌉
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋⌈⇑ₛ⇑ₛσ⌉] v(0) :=
  by
    simp [substitute]
    apply And.intro
    · simp [substitute_var]
      rfl
    · simp [substitute_var]
      rfl

theorem helper_subst_nat_elim {leq : l ≤ n} {s : Tm l} {A : Tm (n + 2)} :
    A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌈⇑ₛ⇑ₛ(s/ₙhleq)⌉
    = A⌈⇑ₛ(s/ₙhleq)⌉⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ :=
  by
    simp [substitution_comp_ρσ]
    simp [substitution_comp]
    simp [comp_weaken_substitute]
    simp [comp_substitute_substitute]
    simp [weakening_id]
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
        simp [shift_tm]
        simp [←substitution_conv_var]
        simp [←substitution_comp_σρ]
        simp [←substitution_comp]
        simp [weakening_id]
        simp [substitution_conv_shift_id_conv]
