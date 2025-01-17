import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

-- If Γ, x:A ` J and Γ ` A = B : type then Γ, x:B ` J

theorem context_conv_is_equal_type :
    IsEqualType (Γ ⬝ A) S T → IsEqualType Γ A B 
    → IsEqualType (Γ ⬝ B) S T :=
  by
    intro hJ hAB
    have hA := ctx_extr (boundary_ctx_type_eq hJ)
    have hA' := HasType.var hA rfl
    sorry

