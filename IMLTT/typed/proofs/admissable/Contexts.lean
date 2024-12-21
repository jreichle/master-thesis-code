import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

import aesop

theorem defeq_is_term' : 
    (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a' ∶ A :=
  by
    intro haaA
    match haaA with
    | _ => sorry

theorem context_conv_has_type : 
    (Γ ⬝ A ⊢ b ∶ B) → Γ ⊢ A ≡ A' type → Γ ⬝ A' ⊢ b ∶ B :=
  sorry

theorem context_conv_is_equal_term : 
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) → Γ ⊢ A ≡ A' type → Γ ⬝ A' ⊢ b ≡ b' ∶ B :=
  sorry

-- TODO: try mutual: symm and context conv
mutual
  theorem defeq_is_type' : Γ ⊢ A ≡ A' type → Γ ⊢ A' type :=
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
      | .iden_form_eq hAA haA haA' =>
        apply IsType.iden_form
        · apply defeq_is_term' (IsEqualTerm.ty_conv_eq haA hAA)
        · apply defeq_is_term' haA'
      | .univ_form_eq hiC =>
          apply IsType.univ_form
          apply hiC
      | .univ_elim_eq hAAU =>
          apply IsType.univ_elim
          apply defeq_is_term' hAAU

  theorem context_conv_is_equal_type :
      Γ ⬝ A ⊢ B ≡ B' type → Γ ⊢ A ≡ A' type → Γ ⬝ A' ⊢ B ≡ B' type :=
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


--   theorem context_conv_is_equal_type_TEST : IsEqualType (Γ ⬝ A) B B' → IsEqualType Γ A A'
--                                             → IsEqualType (Γ ⬝ A') B B' :=
--     by
--       intro hBB hAA
--       rw [substitute_type_eq_inverse] -- FIXME: substitution_type_eq_id correct?
--       apply substitution_type_eq
--       · apply context_conv_has_type -- FIXME: sorry dependency
--         · have hA := defeq_is_type hAA
--           apply HasType.var hA
--         · apply hAA
--       · rw [substitution_id_lift] -- FIXME: substitution_type_eq_id correct?
--         rw [substitution_id_lift]
--         rw [lifting_ctx_one_term]
--         apply weakening_type_eq
--         · rw [context_extend_eq_type] at hBB
--           apply hBB
--         · apply defeq_is_type' hAA
end

-- theorem context_conv_is_equal_type_gen :
--     IsEqualType ((Γ ⬝ A); Δ) B B'
--     → IsEqualType Γ A A'
--     → IsEqualType ((Γ ⬝ A'); Δ) B B' :=
--   by
--     intro hBB
--     intro hAA
--     match hBB with
--     | .unit_form_eq hiC =>
--       apply IsEqualType.unit_form_eq
--       sorry
--     | .pi_form_eq hAA' hBB' =>
--       apply IsEqualType.pi_form_eq
--       · apply context_conv_is_equal_type_gen hAA' hAA
--       · sorry -- apply context_conv_is_equal_type_gen hBB' hAA
--     | _ => sorry

theorem context_conv_is_ctx : 
    Γ ⬝ A ctx → Γ ⊢ A ≡ A' type → Γ ⬝ A' ctx :=
  fun hiCA : IsCtx (Γ ⬝ A) ↦
    fun hAA : IsEqualType Γ A A' ↦
      match hiCA with
      | .extend hiC _ =>
        by
          apply IsCtx.extend
          · apply hiC
          · apply defeq_is_type' hAA

theorem context_conv_is_type :
    Γ ⬝ A ⊢ B type → Γ ⊢ A ≡ A' type → Γ ⬝ A' ⊢ B type :=
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
    | IsType.iden_form haA haA' =>
      by
        sorry
    | IsType.univ_form hiC =>
      by
        sorry
    | IsType.univ_elim hAU =>
      by
        sorry
