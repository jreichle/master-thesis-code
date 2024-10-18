import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.BoundaryConditions
import IMLTT.proofs.admissable.Contexts

/- # Definitional Equality is Equivalence Relation -/

mutual
  theorem defeq_term_refl : HasType Γ a A → IsEqualTerm Γ a a A :=
    by
      intro haA
      match haA with
      | .var hA =>
        apply IsEqualTerm.var_eq
        apply hA
      | .unit_intro hiC =>
        apply IsEqualTerm.unit_intro_eq hiC
      | .pi_intro hbB =>
        apply IsEqualTerm.pi_intro_eq
        · apply defeq_type_refl
          have hiCA := boundary_ctx_term hbB
          match hiCA with
          | .extend hiC hA =>
            apply hA
        · apply defeq_type_refl
          apply boundary_term_type
          apply hbB
        · apply defeq_term_refl
          apply hbB
      | .sigma_intro haA' hbB' =>
        apply IsEqualTerm.sigma_intro_eq
        · apply defeq_type_refl
          apply boundary_term_type haA'
        · apply defeq_type_refl
          have hBs := boundary_term_type hbB'
          apply boundary_subs_type_ctx hBs haA'
        · apply defeq_term_refl
          apply haA'
        · apply defeq_term_refl
          apply hbB'
      | .iden_intro hA =>
        apply IsEqualTerm.iden_intro_eq
        apply defeq_term_refl
        apply hA
      -- univ start
      | .univ_unit hiC =>
        apply IsEqualTerm.univ_unit_eq hiC
      | .univ_empty hiC =>
        apply IsEqualTerm.univ_empty_eq hiC
      | .univ_pi hAU hBU =>
        apply IsEqualTerm.univ_pi_eq
        · apply defeq_term_refl
          apply hAU
        · apply defeq_term_refl
          apply hBU
      | .univ_sigma hAU hBU =>
        apply IsEqualTerm.univ_sigma_eq
        · apply defeq_term_refl
          apply hAU
        · apply defeq_term_refl
          apply hBU
      | .univ_iden hAU haA haA' =>
        apply IsEqualTerm.univ_iden_eq
        · apply defeq_term_refl
          apply hAU
        · apply defeq_term_refl
          apply haA
        · apply defeq_term_refl
          apply haA'
      -- univ end
      | .unit_elim hA haA hbUn =>
        apply IsEqualTerm.unit_elim_eq
        · apply defeq_type_refl
          apply hA
        · apply defeq_term_refl
          apply haA
        · apply defeq_term_refl
          apply hbUn
      | .empty_elim hA hbEm =>
        apply IsEqualTerm.empty_elim_eq
        · apply defeq_type_refl
          apply hA
        · apply defeq_term_refl
          apply hbEm
      | .pi_elim hfPi haA =>
        apply IsEqualTerm.pi_elim_eq
        · apply defeq_type_refl
          apply boundary_term_type hfPi
        · apply defeq_term_refl
          apply haA
        · apply defeq_term_refl
          apply hfPi
      | .sigma_elim hpPi hC hcC =>
        apply IsEqualTerm.sigma_elim_eq
        · apply defeq_type_refl
          apply boundary_term_type hpPi
        · apply defeq_term_refl
          apply hpPi
        · apply defeq_type_refl
          apply hC
        · apply defeq_term_refl
          apply hcC
      | .iden_elim hB hbB hpI =>
        apply IsEqualTerm.iden_elim_eq
        · apply defeq_type_refl
          apply hB
        · apply defeq_term_refl
          apply hbB
        · apply defeq_term_refl
          apply hpI
      | .ty_conv haA hAB =>
        apply IsEqualTerm.ty_conv_eq
        · apply defeq_term_refl
          apply haA
        · apply hAB

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
end

theorem defeq_term_symm : IsEqualTerm Γ a b A → IsEqualTerm Γ b a A :=
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
    | .pi_intro_eq hAA hBB hbbB => sorry
    | .pi_elim_eq hPiPi haaA hffPi => sorry
    | .sigma_intro_eq hAA hBB haaA hbbB => sorry
    | .sigma_elim_eq hSiSi hppSi hCC hccC => sorry
    | .iden_intro_eq hAA  => sorry
    | .iden_elim_eq hAA hBB hbbB => sorry
    | .ty_conv_eq habA hAB => sorry

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


theorem defeq_term_trans : IsEqualTerm Γ a b A → IsEqualTerm Γ b c A → IsEqualTerm Γ a c A :=
  by
    intro habA hbcA
    sorry
    -- match habA with
    -- | .var_eq hA => sorry
    -- | .unit_comp hC hcC => sorry
    -- | .pi_comp hbB haA => sorry
    -- | .sigma_comp haA hbB hC hcC => sorry
    -- | .iden_comp hB hbB haA => sorry
    -- | .unit_intro_eq hiC => sorry
    -- | .unit_elim_eq hAA haaA hbbUn => sorry
    -- | .empty_elim_eq hAA hbbEm => sorry
    -- | .pi_intro_eq hAA hBB hbbB => sorry
    -- | .pi_elim_eq hPiPi haaA hffPi => sorry
    -- | .sigma_intro_eq hAA hBB haaA hbbB => sorry
    -- | .sigma_elim_eq hSiSi hppSi hCC hccC => sorry
    -- | .iden_intro_eq hAA  => sorry
    -- | .iden_elim_eq hAA hBB hbbB => sorry
    -- | .ty_conv_eq habA hAB => sorry


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
