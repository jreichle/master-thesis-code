import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.admissable.Weakening

/- # Boundary conditions -/

theorem boundary_ctx_term : HasType Γ a A → IsCtx Γ :=
  sorry

theorem boundary_ctx_term_eq : IsEqualTerm Γ a b A → IsCtx Γ :=
  sorry

theorem boundary_ctx_type : IsType Γ A → IsCtx Γ :=
  by
    intro hA
    match hA with
    | .unit_form hiC =>
      apply hiC
    | .empty_form hiC =>
      apply hiC
    | .pi_form hA hB =>
      apply boundary_ctx_type hA
    | .sigma_form hA hB =>
      apply boundary_ctx_type hA
    | .iden_form haA haA' =>
      apply boundary_ctx_term haA
    | .univ_form hiC =>
      apply hiC
    | .univ_elim hAU =>
      apply boundary_ctx_term hAU

theorem boundary_ctx_type_eq : IsEqualType Γ A B → IsCtx Γ :=
  sorry

theorem boundary_term_type : HasType Γ a A → IsType Γ A :=
  sorry

theorem boundary_equal_term_type : IsEqualTerm Γ a a' A → IsType Γ A :=
  sorry

/- # Closed term check -/

theorem closed_lift_eq : lift l j tm = tm :=
  sorry
