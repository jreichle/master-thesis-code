import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules

/- # Weakening -/

/- # Definitional Equality -/

#print IsEqualTerm

theorem defeq_is_term : IsEqualTerm Γ a a' A → HasType Γ a A :=
  fun haaA : IsEqualTerm Γ a a' A ↦ 
  match haaA with
  | _ => sorry

theorem defeq_is_term' : IsEqualTerm Γ a a' A → HasType Γ a' A :=
  fun haaA : IsEqualTerm Γ a a' A ↦ 
  match haaA with
  | _ => sorry

theorem defeq_is_type : IsEqualType Γ A A' → IsType Γ A :=
  fun hAA : IsEqualType Γ A A' ↦
  match hAA with
  | .unit_form_eq hiC =>
    by
      apply IsType.unit_form hiC
  | .empty_form_eq hiC =>
    by
      apply IsType.empty_form hiC
  | .pi_form_eq hAA hBB =>
    by
      apply IsType.pi_form
      · apply defeq_is_type hAA
      · apply defeq_is_type hBB
  | .sigma_form_eq hAA hBB =>
    by
      apply IsType.sigma_form
      · apply defeq_is_type hAA
      · apply defeq_is_type hBB
    | .iden_form_eq hAA =>
      by
        apply IsType.iden_form
        apply defeq_is_type hAA
    | .univ_form_eq hiC => 
      by
        apply IsType.univ_form
        apply hiC
    | .univ_elim_eq hAAU =>
      by
        apply IsType.univ_elim
        apply defeq_is_term hAAU

theorem defeq_is_type' : IsEqualType Γ A A' → IsType Γ A' :=
  fun hAA : IsEqualType Γ A A' ↦
  match hAA with
  | .unit_form_eq hiC =>
    by
      apply IsType.unit_form hiC
  | .empty_form_eq hiC =>
    by
      apply IsType.empty_form hiC
  | .pi_form_eq hAA hBB =>
    by
      apply IsType.pi_form
      · apply defeq_is_type' hAA
      · match hBB with
        | .unit_form_eq hiC => 
          apply IsType.unit_form
          apply IsCtx.extend
          · cases hiC with
            | extend hiC hA =>
              apply hiC
          · apply defeq_is_type' hAA
        | .empty_form_eq hiC =>
          apply IsType.empty_form
          apply IsCtx.extend
          · cases hiC with
            | extend hiC hA =>
              apply hiC
          · apply defeq_is_type' hAA
        | .pi_form_eq hAA' hBB' =>
          apply IsType.pi_form
          · apply defeq_is_type'
            · sorry
            · sorry
          · sorry
        | _ => sorry
  | .sigma_form_eq hAA hBB =>
    by
      apply IsType.sigma_form
      · apply defeq_is_type' hAA
      · apply sorry
    | .iden_form_eq hAA =>
      by
        apply IsType.iden_form
        apply defeq_is_type hAA
    | .univ_form_eq hiC => 
      by
        apply IsType.univ_form
        apply hiC
    | .univ_elim_eq hAAU =>
      by
        apply IsType.univ_elim
        apply defeq_is_term' hAAU

theorem defeq_context_conv : IsEqualType (Γ ⬝ A) B B' → IsEqualType Γ A A'
                             → IsEqualType (Γ ⬝ A') B B' :=
  fun hBB : IsEqualType (Γ ⬝ A) B B' ↦
    fun hAA : IsEqualType Γ A A' ↦
    match hBB with
    | .unit_form_eq hiC =>
      by
        apply IsEqualType.unit_form_eq
        apply IsCtx.extend
        · cases hiC with
          | extend hiC hA => apply hiC
        · apply defeq_is_type' (hAA)
    | .empty_form_eq hiC =>
      by
        apply IsEqualType.empty_form_eq
        apply IsCtx.extend
        · cases hiC with
          | extend hiC hA => apply hiC
        · apply defeq_is_type' (hAA)
    | .pi_form_eq hAA hBB =>
      by
        sorry
    | _ => sorry

/- # Definitional Equality is Equivalence Relation -/

/- # terms -/

#print HasType

theorem defeq_term_refl : HasType Γ a A → IsEqualTerm Γ a a A :=
  fun haA : HasType Γ a A ↦
    match haA with
    | .var hA => sorry
    | .weak hvA hB => sorry
    | .unit_intro hiC =>
      by 
        
    | .pi_intro hB => sorry
    | .sigma_intro hA hB => sorry
    | .iden_intro hA => sorry
    | .univ_unit hiC => sorry
    | .univ_empty hiC => sorry
    | .univ_pi hAU hBU => sorry
    | .univ_sigma hAU hBU => sorry
    | .univ_iden hAU => sorry
    | .unit_elim hA haA hbUn => sorry
    | .empty_elim hA hbEm => sorry
    | .pi_elim hfPi haA => sorry
    | .sigma_elim hpSi hC hcC => sorry
    | .iden_elim hB hbB => sorry
    | .ty_conv haA hAB => sorry

#print IsEqualTerm

theorem defeq_term_symm : IsEqualTerm Γ a b A → IsEqualTerm Γ b a A :=
  fun habA : IsEqualTerm Γ a b A ↦
    match habA with 
    | .unit_comp hC hcC => sorry
    | .pi_comp hbB haA => sorry
    | .sigma_comp haA hbB hC hcC => sorry
    | .iden_comp hB hbB => sorry
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

theorem defeq_term_trans : IsEqualTerm Γ a b A → IsEqualTerm Γ b c A → IsEqualTerm Γ a c A :=
  fun habA : IsEqualTerm Γ a b A ↦
    match habA with
    | .unit_comp hC hcC => sorry
    | .pi_comp hbB haA => sorry
    | .sigma_comp haA hbB hC hcC => sorry
    | .iden_comp hB hbB => sorry
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

/- # types -/

#print IsType

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
    | IsType.iden_form hA =>
      by 
        apply IsEqualType.iden_form_eq
        apply defeq_type_refl hA
    | IsType.univ_form hiC =>
      by
        apply IsEqualType.univ_form_eq hiC
    | IsType.univ_elim hAU =>
      by
        apply IsEqualType.univ_elim_eq
        apply defeq_term_refl hAU

#print IsEqualType

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
        · have hBB' := by apply defeq_context_conv hBB hAA
          apply defeq_type_symm hBB'
    | .sigma_form_eq hAA hBB =>
      by
        apply IsEqualType.sigma_form_eq
        · apply defeq_type_symm hAA
        · have hBB' := by apply defeq_context_conv hBB hAA
          apply defeq_type_symm hBB'
    | .iden_form_eq hAA =>
      by
        apply IsEqualType.iden_form_eq hAA
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
          · have hBBs := defeq_context_conv hBBc (defeq_type_symm hAA)
            apply defeq_type_trans hBB hBBs
        | univ_elim_eq hPIc => sorry
       --  sorry -- TODO: stuck? looping here -> use term transitivity
       --                                     -> inversions lemma (C gleich Pi), dann rausziehen
    | .sigma_form_eq hAA hBB =>
      by 
        sorry    
    | .iden_form_eq hAA =>
      by 
        apply hBC
    | .univ_form_eq hic => 
      by 
        apply hBC
    | .univ_elim_eq hAAU =>
      by 
        sorry
