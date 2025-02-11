import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

import aesop

-- different weakening

theorem weakening_inv :
    Γ ⬝ A ⊢ B⌊↑ₚidₚ⌋ ≡ B'⌊↑ₚidₚ⌋ type
    → Γ ⊢ B ≡ B' type :=
  by
    intro h1
    sorry

theorem context_conv_is_ctx :
    Γ ⊢ A' type
    → Γ ⬝ A ctx → Γ ⊢ A ≡ A' type
    → Γ ⬝ A' ctx :=
  by
    intro hA' hiCA hAA
    match hiCA with
    | .extend hiC _ =>
        apply IsCtx.extend
        · apply hiC
        · apply hA'

theorem context_conv_is_equal_type :
    Γ ⊢ A' type
    → Γ ⬝ A ⊢ B ≡ B' type → Γ ⊢ A ≡ A' type
    → Γ ⬝ A' ⊢ B ≡ B' type :=
  by
    intro hA' hBB hAA
    have h1 := boundary_ctx_type_eq hBB
    have h2 := ctx_extr h1
    have h3 := HasType.var h2
    have h4 := weakening_type_eq hAA h2
    have h5 := HasType.ty_conv h3 h4
    have h6 := weakening_second_type_eq hBB hA'
    exact weakening_inv h6
