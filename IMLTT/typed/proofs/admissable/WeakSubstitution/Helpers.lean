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

theorem helper_weak_subst_nat_elim {leq : l ≤ n} {s : Tm l} {A : Tm (n + 1)} :
    A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌈⇑ₛ⇑ₛ(s↑/ₙhleq)⌉
    = A⌈⇑ₛ(s↑/ₙhleq)⌉⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ :=
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
