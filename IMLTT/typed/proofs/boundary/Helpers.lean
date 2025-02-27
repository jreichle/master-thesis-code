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
