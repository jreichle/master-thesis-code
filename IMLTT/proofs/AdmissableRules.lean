import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules


/- # Universe and Pi/Sigma -/

theorem pi_univ_backwards_fst : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U → IsEqualType Γ A A' :=
  fun hPiPiU : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U ↦
   by
    match hPiPiU with
    | _ => sorry

theorem pi_univ_backwards_snd : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U → IsEqualType (Γ ⬝ A) B B' :=
  fun hPiPiU : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U ↦
   by
    match hPiPiU with
    | .pi_form_eq 
    | _ => sorry

/- # Weakening -/

-- TODO: formulate theorems for all forms of judgment
-- TODO: substitution property in Harpter and Pfenning

/- # Definitional Equality - Inverse of Reflexivity -/

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
    by
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

theorem defeq_is_type' : IsEqualType Γ A A' → IsType Γ A' :=
  fun hAA : IsEqualType Γ A A' ↦
    by
      match hAA with
      | .unit_form_eq hiC =>
          apply IsType.unit_form hiC
      | .empty_form_eq hiC =>
          apply IsType.empty_form hiC
      | .pi_form_eq hAA hBB =>
          apply IsType.pi_form
          · apply defeq_is_type' hAA
          · have hA := defeq_is_type' hAA
            have hB := defeq_is_type' hBB
            apply defeq_is_type'
      | .sigma_form_eq hAA hBB =>
          apply IsType.sigma_form
          · apply defeq_is_type' hAA
          · apply sorry
      | .iden_form_eq hAA =>
          apply IsType.iden_form
          apply defeq_is_type hAA
      | .univ_form_eq hiC => 
          apply IsType.univ_form
          apply hiC
      | .univ_elim_eq hAAU =>
          apply IsType.univ_elim
          apply defeq_is_term' hAAU

/- # Definitional Equality -  Context Conversion -/

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
        cases a with
        | tt =>
          apply IsEqualTerm.unit_intro_eq hiC
        | _ => sorry
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

mutual
  theorem defeq_is_typex : IsEqualType Γ A A' → IsType Γ A' :=
    fun hAA : IsEqualType Γ A A' ↦
      by
        match hAA with
        | .unit_form_eq hiC =>
            apply IsType.unit_form hiC
        | .empty_form_eq hiC =>
            apply IsType.empty_form hiC
        | .pi_form_eq hAA hBB =>
            apply IsType.pi_form
            · apply defeq_is_typex hAA
            · have hBB' :=
                context_conv_is_equal_type hBB hAA
              apply defeq_is_typex hBB'
        | .sigma_form_eq hAA hBB =>
            apply IsType.sigma_form
            · apply defeq_is_typex hAA
            · have hBB' :=
                context_conv_is_equal_type hBB hAA
              apply defeq_is_typex hBB'
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
    fun hBB : IsEqualType (Γ ⬝ A) B B' ↦
      fun hAA : IsEqualType Γ A A' ↦
        by
          match hBB with
          | .unit_form_eq hiC =>
            apply IsEqualType.unit_form_eq
            apply IsCtx.extend
            · cases hiC with
              | extend hiC hA => apply hiC
            · apply defeq_is_typex (hAA)
          | .empty_form_eq hiC =>
            apply IsEqualType.empty_form_eq
            apply IsCtx.extend
            · cases hiC with
              | extend hiC hA => apply hiC
            · apply defeq_is_typex (hAA)
          | .pi_form_eq hAA' hBB' =>
            sorry
            -- apply context_conv_is_equal_type
            -- · apply IsEqualType.pi_form_eq
            --   · apply context_conv_is_equal_type hAA' hAA
            --   · have hPi := IsEqualType.pi_form_eq hAA' hBB'
            --     have hPi' := context_conv_is_equal_type hPi hAA
            --     cases hPi' with
            --     | pi_form_eq hAAc hBBc =>
            --       apply hBBc
            --     | univ_elim_eq hBBU =>
            --       apply pi_univ_backwards_snd hBBU
            -- · sorry
          | _ => sorry
end

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
          · have hBBs := context_conv_is_equal_type hBBc (defeq_type_symm hAA)
            apply defeq_type_trans hBB hBBs
        | univ_elim_eq hPiC =>
          apply IsEqualType.univ_elim_eq
          have hPiPi := (IsEqualType.pi_form_eq hAA hBB)
          apply defeq_term_trans hPiPi hPiC 
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
