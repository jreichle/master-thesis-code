import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Contexts

import aesop

theorem defeq_symm_term : 
    (Γ ⊢ a ≡ b ∶ A) → Γ ⊢ b ≡ a ∶ A :=
  by
    intro habA
    match habA with
    | .var_eq hA => sorry
    | .unit_comp hC hcC => sorry
    | .pi_comp hbB haA => sorry
    | .sigma_comp haA hbB hC hcC => sorry
    | .iden_comp hB hbB haA  => sorry
    | .unit_intro_eq hiC => sorry
    | .unit_elim_eq hAA haaA hbbUn => sorry
    | .empty_elim_eq hAA hbbEm => sorry
    | .pi_intro_eq hbbB => sorry
    | .pi_elim_eq haaA hffPi => sorry
    | .sigma_intro_eq haaA hbbB => sorry
    | .sigma_elim_eq hSiSi hppSi hCC hccC => sorry
    | .iden_intro_eq hAA haaA  => sorry
    | .iden_elim_eq hBB hbbB hIdId hppId => sorry
    | .univ_unit_eq hiC => sorry
    | .univ_empty_eq hiC => sorry
    | .univ_pi_eq hAAU hBBU => sorry
    | .univ_sigma_eq hAAU hBBU => sorry
    | .univ_iden_eq hAAU haaA haaA' => sorry
    | .ty_conv_eq habA hAB => sorry

theorem defeq_symm_type : 
    Γ ⊢ A ≡ B type → Γ ⊢ B ≡ A type :=
  fun hABet : IsEqualType Γ A B ↦
    match hABet with
    | .unit_form_eq hic =>
      by
        apply IsEqualType.unit_form_eq hic
    | .empty_form_eq hic =>
      by
        apply IsEqualType.empty_form_eq hic
    | .pi_form_eq hAA hBB =>
      by
        apply IsEqualType.pi_form_eq
        · apply defeq_symm_type hAA
        · have hBB' := by apply context_conv_is_equal_type hBB hAA
          apply defeq_symm_type hBB'
    | .sigma_form_eq hAA hBB =>
      by
        apply IsEqualType.sigma_form_eq
        · apply defeq_symm_type hAA
        · have hBB' := by apply context_conv_is_equal_type hBB hAA
          apply defeq_symm_type hBB'
    | .iden_form_eq hAA haaA haaA' =>
      by
        apply IsEqualType.iden_form_eq
        · apply defeq_symm_type hAA
        · apply IsEqualTerm.ty_conv_eq (defeq_symm_term haaA) hAA
        · apply IsEqualTerm.ty_conv_eq (defeq_symm_term haaA') (defeq_symm_type hAA)
    | .univ_form_eq hic =>
      by
        apply IsEqualType.univ_form_eq hic
    | .univ_elim_eq hAAU =>
      by
        apply IsEqualType.univ_elim_eq
        apply defeq_symm_term
        apply hAAU

