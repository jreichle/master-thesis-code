import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules
import IMLTT.proofs.admissable.AdmissableRules

/- # Definitional Equality - Inverse of Reflexivity -/

theorem defeq_is_term : IsEqualTerm Γ a a' A → HasType Γ a A :=
  by 
    intro haaA
    match haaA with
    | _ => sorry

theorem defeq_is_term' : IsEqualTerm Γ a a' A → HasType Γ a' A :=
  by
    intro haaA
    match haaA with
    | _ => sorry

theorem defeq_is_type : IsEqualType Γ A A' → IsType Γ A :=
  by
    intro hAA
    match hAA with
    | .unit_form_eq hiC =>
        apply IsType.unit_form hiC
    | .empty_form_eq hiC =>
        apply IsType.empty_form hiC
    | .pi_form_eq hAA hBB =>
        apply IsType.pi_form
        · apply defeq_is_type hAA
        · apply defeq_is_type hBB
    | .sigma_form_eq hAA hBB =>
        apply IsType.sigma_form
        · apply defeq_is_type hAA
        · apply defeq_is_type hBB
    | .iden_form_eq hAA =>
        apply IsType.iden_form
        apply defeq_is_type hAA
    | .univ_form_eq hiC => 
        apply IsType.univ_form
        apply hiC
    | .univ_elim_eq hAAU =>
        apply IsType.univ_elim
        apply defeq_is_term hAAU

mutual
  theorem defeq_is_type' : IsEqualType Γ A A' → IsType Γ A' :=
    by
      intro hAA
      match hAA with
      | .unit_form_eq hiC =>
          apply IsType.unit_form hiC
      | .empty_form_eq hiC =>
          apply IsType.empty_form hiC
      | .pi_form_eq hAA hBB =>
          apply IsType.pi_form
          · apply defeq_is_type' hAA
          · have hBB' :=
              context_conv_is_equal_type hBB hAA
            apply defeq_is_type' hBB'
      | .sigma_form_eq hAA hBB =>
          apply IsType.sigma_form
          · apply defeq_is_type' hAA
          · have hBB' :=
              context_conv_is_equal_type hBB hAA
            apply defeq_is_type' hBB'
      | .iden_form_eq hAA =>
          apply IsType.iden_form
          apply defeq_is_type hAA
      | .univ_form_eq hiC => 
          apply IsType.univ_form
          apply hiC
      | .univ_elim_eq hAAU =>
          apply IsType.univ_elim
          apply defeq_is_term' hAAU

  -- TODO: generalize to any spot in context
  theorem context_conv_is_equal_type : IsEqualType (Γ ⬝ A) B B' → IsEqualType Γ A A'
                                       → IsEqualType (Γ ⬝ A') B B' :=
    by
      intro hBB
      intro hAA
      match hBB with
      | .unit_form_eq hiC =>
        apply IsEqualType.unit_form_eq
        apply IsCtx.extend
        · cases hiC with
          | extend hiC hA => apply hiC
        · apply defeq_is_type' (hAA)
      | .pi_form_eq hAA' hBB' =>
        apply IsEqualType.pi_form_eq
        · apply context_conv_is_equal_type hAA' hAA
        · sorry
      | _ => sorry
end

theorem context_conv_is_equal_type_gen : IsEqualType (concat_ctx (Γ ⬝ A) Δ) B B' → IsEqualType Γ A A'
                                      → IsEqualType (concat_ctx (Γ ⬝ A') Δ) B B' :=
  by
    intro hBB
    intro hAA
    match hAA with
    | .unit_form_eq hiC => sorry
    | _ => sorry

theorem context_conv_is_ctx : IsCtx (Γ ⬝ A) → IsEqualType Γ A A'
                              → IsCtx (Γ ⬝ A') :=
  fun hiCA : IsCtx (Γ ⬝ A) ↦
    fun hAA : IsEqualType Γ A A' ↦
      match hiCA with
      | .extend hiC _ =>
        by
          apply IsCtx.extend
          · apply hiC
          · apply defeq_is_type' hAA

-- TODO: recursion on IsEqualType
theorem context_conv_is_type : IsType (Γ ⬝ A) B → IsEqualType Γ A A'
                               → IsType (Γ ⬝ A') B :=
  fun hB : IsType (Γ ⬝ A) B ↦
    fun hAA : IsEqualType Γ A A' ↦
    match hB with
    | .unit_form hiC =>
      by 
        have hiCA' := context_conv_is_ctx hiC hAA
        apply IsType.unit_form hiCA'
    | .empty_form hiC  =>
      by 
        have hiCA' := context_conv_is_ctx hiC hAA
        apply IsType.empty_form hiCA'
    | .pi_form hA hB =>
      by 
        apply IsType.pi_form
        · have hA' := context_conv_is_type hA hAA
          apply hA'
        · sorry -- change with first rfl in first spot and then use correct in second spot
    | IsType.sigma_form hA hB =>
      by 
        sorry
    | IsType.iden_form hA =>
      by 
        sorry
    | IsType.univ_form hiC =>
      by
        sorry
    | IsType.univ_elim hAU =>
      by
        sorry

theorem context_conv_has_type : HasType (Γ ⬝ A) b B → IsEqualType Γ A A'
                                → HasType (Γ ⬝ A') b B :=
  sorry

theorem context_conv_is_equal_term : IsEqualTerm (Γ ⬝ A) b b' B → IsEqualType Γ A A'
                             → IsEqualTerm (Γ ⬝ A') b b' B :=
  sorry
