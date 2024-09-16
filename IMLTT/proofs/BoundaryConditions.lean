import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules

/- # Boundary conditions -/

theorem boundary_ctx_type : IsType Γ A → IsCtx Γ :=
  sorry

theorem boundary_ctx_term : HasType Γ a A → IsCtx Γ :=
  sorry

theorem boundary_ctx_type_eq : IsEqualType Γ A B → IsCtx Γ :=
  sorry

theorem boundary_ctx_term_eq : IsEqualTerm Γ a b A → IsCtx Γ :=
  sorry

