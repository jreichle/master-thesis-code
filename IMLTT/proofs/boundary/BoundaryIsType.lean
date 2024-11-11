import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.admissable.Weakening
import IMLTT.proofs.admissable.Substitution
import IMLTT.proofs.boundary.BoundaryIsCtx

/- # if hasType, then type is well-formed -/

-- TODO: use recursor to merge these proofs

-- TODO: if not provable, major rules changes needed
theorem boundary_term_type : HasType Γ a A → IsType Γ A :=
  by
    intro haA
    match haA with
    | .var hA =>
      apply weakening_type hA hA
    | .unit_intro hiC =>
      apply IsType.unit_form hiC
    | .pi_intro hbB =>
      have hB := boundary_term_type hbB
      apply IsType.pi_form 
      · have hiCA := boundary_ctx_type hB
        apply ctx_extr hiCA
      · apply hB
    | .sigma_intro haA hbB =>
      apply IsType.sigma_form
      · apply boundary_term_type haA
      · have hBs := boundary_term_type hbB
        apply substitution_inv_type
        · rfl
        · apply hBs
        · apply haA
    | .iden_intro hA haA =>
      apply IsType.iden_form haA haA
    -- univ start
    | .univ_unit hiC => 
      apply IsType.univ_form hiC
    | .univ_empty hiC =>
      apply IsType.univ_form hiC
    | .univ_pi hAU hBU =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    | .univ_sigma hAU hBU =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    | .univ_iden hAU haA haA' =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    -- univ end
    | .unit_elim hA haA hb1 =>
      apply substitution_type
      · apply hb1
      · apply hA
    | .empty_elim hA hb0 =>
      apply substitution_type
      · apply hb0
      · apply hA
    | .pi_elim hfPi haA =>
      apply substitution_type
      · apply haA
      · have hPi := boundary_term_type hfPi
        sorry
    | .sigma_elim hPi hpPi hC hcC =>
      apply substitution_type
      · apply hpPi
      · apply hC
    | .iden_elim hB hbB hId hpI =>
      sorry
    | .ty_conv haA hAB =>
      sorry

theorem boundary_equal_term_type : IsEqualTerm Γ a a' A → IsType Γ A :=
  sorry

/-# if substiution works, then adding type to context also -/

theorem boundary_subs_type_ctx : IsType Γ (substitute A (.extend σ b))  → HasType Γ b B
                                 → IsType (Γ ⬝ B) (substitute A (.lift (σ))) :=
  sorry
