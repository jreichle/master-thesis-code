import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules

theorem defeq_term_refl : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    match haA with
    | .var hA =>
      apply IsEqualTerm.var_eq
      apply hA
    | .weak hvA hB => sorry
    | .unit_intro hiC =>
      cases a with
      | tt =>
        apply IsEqualTerm.unit_intro_eq hiC
      | _ => sorry -- FIXME: how?
    | .pi_intro hB =>
      sorry
    | .sigma_intro hA hB => sorry
    | .iden_intro hA => sorry
    | .univ_unit hiC => sorry
    | .univ_empty hiC => sorry
    | .univ_pi hAU hBU => sorry
    | .univ_sigma hAU hBU => sorry
    | .univ_iden hAU haA haA' => sorry
    | .unit_elim hA haA hbUn => sorry
    | .empty_elim hA hbEm => sorry
    | .pi_elim hfPi haA => sorry
    | .sigma_elim hpSi hC hcC => sorry
    | .iden_elim hB hbB hpI => sorry
    | .ty_conv haA hAB => sorry

theorem defeq_term_symm : IsEqualTerm Γ a b A → IsEqualTerm Γ b a A :=
  fun habA : IsEqualTerm Γ a b A ↦
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

theorem defeq_term_trans : IsEqualTerm Γ a b A → IsEqualTerm Γ b c A → IsEqualTerm Γ a c A :=
  fun habA : IsEqualTerm Γ a b A ↦
    match habA with
    | .var_eq hA => sorry
    | .unit_comp hC hcC => sorry
    | .pi_comp hbB haA => sorry
    | .sigma_comp haA hbB hC hcC => sorry
    | .iden_comp hB hbB haA => sorry
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

