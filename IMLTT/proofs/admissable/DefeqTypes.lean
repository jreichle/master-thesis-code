import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules
import IMLTT.proofs.admissable.DefeqTerms
import IMLTT.proofs.admissable.Contexts

/- # Definitional Equality is Equivalence Relation -/

theorem defeq_type_refl : IsType Γ A → IsEqualType Γ A A :=
  fun hA : IsType Γ A ↦
    match hA with
    | .unit_form hiC =>
      by 
        apply IsEqualType.unit_form_eq hiC
    | .empty_form hiC  =>
      by 
        apply IsEqualType.empty_form_eq hiC
    | .pi_form hA hB =>
      by 
        apply IsEqualType.pi_form_eq
        · apply defeq_type_refl hA
        · apply defeq_type_refl hB
    | IsType.sigma_form hA hB =>
      by 
        apply IsEqualType.sigma_form_eq
        · apply defeq_type_refl hA
        · apply defeq_type_refl hB
    | IsType.iden_form haA haA' =>
      by 
        apply IsEqualType.iden_form_eq
        · apply defeq_term_refl haA
        · apply defeq_term_refl haA'
    | IsType.univ_form hiC =>
      by
        apply IsEqualType.univ_form_eq hiC
    | IsType.univ_elim hAU =>
      by
        apply IsEqualType.univ_elim_eq
        apply defeq_term_refl hAU

theorem defeq_type_symm : IsEqualType Γ A B → IsEqualType Γ B A :=
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
        · apply defeq_type_symm hAA
        · have hBB' := by apply context_conv_is_equal_type hBB hAA
          apply defeq_type_symm hBB'
    | .sigma_form_eq hAA hBB =>
      by
        apply IsEqualType.sigma_form_eq
        · apply defeq_type_symm hAA
        · have hBB' := by apply context_conv_is_equal_type hBB hAA
          apply defeq_type_symm hBB'
    | .iden_form_eq haaA haaA' =>
      by
        apply IsEqualType.iden_form_eq
        · apply defeq_term_symm haaA
        · apply defeq_term_symm haaA'
    | .univ_form_eq hic =>
      by
        apply IsEqualType.univ_form_eq hic
    | .univ_elim_eq hAAU =>
      by
        apply IsEqualType.univ_elim_eq
        apply defeq_term_symm
        apply hAAU

theorem defeq_type_trans : IsEqualType Γ A B → IsEqualType Γ B C → IsEqualType Γ A C :=
  fun hAB : IsEqualType Γ A B ↦
    fun hBC : IsEqualType Γ B C ↦
    match hAB with
    | .unit_form_eq hic =>
      by 
        apply hBC
    | .empty_form_eq hic =>
      by 
        apply hBC
    | .pi_form_eq hAA hBB =>
      by
        cases hBC with
        | pi_form_eq hAAc hBBc =>
          apply IsEqualType.pi_form_eq
          · apply defeq_type_trans hAA hAAc
          · have hBBs := context_conv_is_equal_type hBBc (defeq_type_symm hAA)
            apply defeq_type_trans hBB hBBs
        | univ_elim_eq hPiC =>
          apply IsEqualType.univ_elim_eq
          have hPiPi := (IsEqualType.pi_form_eq hAA hBB)
          sorry -- apply defeq_term_trans hPiPi hPiC 
       --  sorry -- TODO: stuck? looping here -> use term transitivity
       --                                     -> inversions lemma (C gleich Pi), dann rausziehen
    | .sigma_form_eq hAA hBB =>
      by 
        sorry    
    | .iden_form_eq haaA haaA' =>
      by 
        sorry
    | .univ_form_eq hic => 
      by 
        apply hBC
    | .univ_elim_eq hAAU =>
      by 
        sorry
