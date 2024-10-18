import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.admissable.Weakening

/- # Boundary conditions -/


theorem boundary_ctx_type' : IsType Γ A → IsCtx Γ := sorry
mutual
  theorem boundary_ctx_term : HasType Γ a A → IsCtx Γ :=
    by
      intro haA
      match haA with
      | .var hA =>
        have hiC := boundary_ctx_type' hA
        apply IsCtx.extend hiC hA
      -- | .weak hvA hB =>
      --   have hiC := boundary_ctx_term hvA
      --   apply IsCtx.extend hiC hB
      | .unit_intro hiC => --> base
        apply hiC
      | .pi_intro hbB =>
        have hiCA := boundary_ctx_term hbB
        match hiCA with
        | .extend hiC  hA => 
          apply hiC
      | .sigma_intro hA hB =>
        have hiC := boundary_ctx_term hA
        apply hiC
      | .iden_intro hA =>
        have hiC := boundary_ctx_term hA
        apply hiC
      | .univ_unit hiC =>
        apply hiC
      | .univ_empty hiC =>
        apply hiC
      | .univ_pi hAU hBU =>
        have hiC := boundary_ctx_term hAU
        apply hiC
      | .univ_sigma hAU hBU =>
        have hiC := boundary_ctx_term hAU
        apply hiC
      | .univ_iden hAU haA haA' =>
        have hiC := boundary_ctx_term hAU
        apply hiC
      | .unit_elim hA haA hbUn =>
        have hiC := boundary_ctx_term haA
        apply hiC
      | .empty_elim hA hbEm =>
        have hiC := boundary_ctx_term hbEm
        apply hiC
      | .pi_elim hfPi haA =>
        have hiC := boundary_ctx_term haA
        apply hiC
      | .sigma_elim hpSi hC hcC =>
        have hiC := boundary_ctx_term hpSi
        apply hiC
      | .iden_elim hB hbB hpI =>
        have hiC := boundary_ctx_term hpI
        apply hiC
      | .ty_conv haA hAB =>
        have hiC := boundary_ctx_term haA
        apply hiC

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
end

mutual
  theorem boundary_ctx_term_eq : IsEqualTerm Γ a b A → IsCtx Γ :=
    sorry

  theorem boundary_ctx_type_eq : IsEqualType Γ A A → IsCtx Γ :=
    by
      intro hAA
      match hAA with
      | .unit_form_eq hiC =>
        apply hiC
      | .empty_form_eq hiC =>
        apply hiC
      | .pi_form_eq hAA' hBB' =>
        apply boundary_ctx_type_eq hAA'
      | .sigma_form_eq hAA' hBB' =>
        apply boundary_ctx_type_eq hAA'
      | .iden_form_eq haa haa' =>
        apply boundary_ctx_term_eq haa
      | .univ_form_eq hiC =>
        apply hiC
      | .univ_elim_eq hAAU =>
        apply boundary_ctx_term_eq hAAU
end

/- # if hasType, then type is well-formed -/

theorem boundary_term_type : HasType Γ a A → IsType Γ A :=
  sorry

theorem boundary_equal_term_type : IsEqualTerm Γ a a' A → IsType Γ A :=
  sorry

/-# if substiution works, then adding type to context also -/

theorem boundary_subs_type_ctx : IsType Γ (substitute A (.extend σ' b))  → HasType Γ b B
                                 → IsType (Γ ⬝ B) A :=
  sorry
