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

theorem shift_weaken_from {hl : l ≤ n} :
    A⌊↑ₚidₚ⌋⌊weaken_from (n + 1) l⌋ = A⌊weaken_from n l⌋⌊↑ₚidₚ⌋ :=
  by
    simp [weaken_from]
    split
    case isTrue hT =>
      simp [weakening_comp]
      simp [comp_weaken]
      rw [←weakening_shift_id]
      rw [←weakening_comp]
      rw [weakening_id]
      rw [weakening_shift_id]
    case isFalse hF =>
      omega

theorem weak_subst_sigma_C {leq : l ≤ n}:
    C⌊weaken_from (n + 1) l⌋⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ =
    C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌊weaken_from (n + 1 + 1) l⌋ :=
  by
    simp [substitution_comp_ρσ]
    simp [substitution_comp_σρ]
    rw [←lift_weaken_from]
    · apply substitution_var_substitute
      intro x
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          rw [←lift_weaken_from]
          · rw [←lift_weaken_from]
            · simp [comp_weaken_substitute]
              simp [comp_substitute_weaken]
              simp [substitute]
              simp [substitute_var]
              simp [weaken]
              simp [weaken_var]
              aesop
            · omega
          · omega
        | succ i' =>
          rw [←lift_weaken_from]
          · rw [←lift_weaken_from]
            · simp [comp_weaken_substitute]
              simp [comp_substitute_weaken]
              simp [substitute]
              simp [substitute_var]
              simp [←substitution_conv_var]
              rw [←substitution_comp_σρ]
              simp [comp_weaken]
              rw [←weakening_shift_id]
              rw (config := {occs := .pos [2]}) [←weakening_shift_id]
              rw [←weakening_comp]
              rw [weakening_id]
              rw (config := {occs := .pos [1]}) [weakening_shift_id]
              rfl
            · omega
          · omega
    · exact leq

theorem weak_subst_sigma_c :
    c⌈(ₛidₚ), a, b⌉⌊ρ⌋
    = c⌊lift_weak_n 2 ρ⌋⌈(ₛidₚ), (a⌊ρ⌋), (b⌊ρ⌋)⌉ :=
  by
    rw [substitution_comp_ρσ]
    rw [substitution_comp_σρ]
    apply substitution_var_substitute
    intro x
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [←substitution_comp_σρ]
      simp [weaken]
      simp [weakening_var_lift_n_id]
      simp [←weakening_conv_var]
      simp [weakening_id]
    | shift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]
      apply substitution_var_substitute
      intro x
      rw [←substitution_conv_shift_id]
      cases x with
      | mk i hFin =>
        induction i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          rw [←weakening_shift_id]
          rw (config := {occs := .pos [2]}) [←weakening_shift_id]
          simp [weakening_id]
          rfl
        | succ i' hInd =>
          simp [substitute]
          simp [substitute_var]
          cases i' with
          | zero =>
            simp [←substitution_conv_var]
            rw [←substitution_comp_ρσ]
            simp [substitute]
            simp [substitute_var]
            simp [weakening_shift_id]
            rfl
          | succ j =>
            simp [substitute_var]
            cases j with
            | zero =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
            | succ j' =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
    | lift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]

theorem weak_subst_iden_elim :
    B⌈(ₛidₚ), a, b, c⌉⌊ρ⌋
    = B⌊lift_weak_n 3 ρ⌋⌈(ₛidₚ), (a⌊ρ⌋), (b⌊ρ⌋), (c⌊ρ⌋)⌉ :=
  by
    rw [substitution_comp_ρσ]
    rw [substitution_comp_σρ]
    apply substitution_var_substitute
    intro x
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [←substitution_comp_σρ]
      simp [weaken]
      simp [weakening_var_lift_n_id]
      simp [←weakening_conv_var]
      simp [weakening_id]
    | shift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]
      apply substitution_var_substitute
      intro x
      rw [←substitution_conv_shift_id]
      cases x with
      | mk i hFin =>
        induction i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          rw [←weakening_shift_id]
          rw (config := {occs := .pos [2]}) [←weakening_shift_id]
          simp [weakening_id]
          rfl
        | succ i' hInd =>
          simp [substitute]
          simp [substitute_var]
          cases i' with
          | zero =>
            simp [←substitution_conv_var]
            rw [←substitution_comp_ρσ]
            simp [substitute]
            simp [substitute_var]
            simp [weakening_shift_id]
            rfl
          | succ j =>
            simp [substitute_var]
            cases j with
            | zero =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
            | succ j' =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
    | lift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]

theorem helper_weak_iden_propagate_weak {leq : l ≤ n} :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌊weaken_from (n + 1 + 1) l⌋
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋⌊weaken_from (n + 1 + 1) l⌋] v(0) :=
  by
    rw [←lift_weaken_from]
    · rw [←lift_weaken_from]
      · simp [weaken]
        simp [weaken_var]
        apply And.intro
        · rfl
        · rfl
      · omega
    · omega

theorem helper_weak_refl_propagate_weak :
    .refl (A⌊weaken_from n l⌋) (a⌊weaken_from n l⌋)
    = (.refl A a)⌊weaken_from n l⌋ :=
  by
    · simp [weaken]

theorem tleq {l : Nat} :
    l + 1 ≤ 0 -> False :=
  by
    intro hLeq
    omega

theorem helper_weak_1 :
    l ≤ x → x + 1 ≤ l → False :=
  by
    intro h1 h2
    omega
