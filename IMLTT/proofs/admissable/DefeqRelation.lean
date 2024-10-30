import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.BoundaryConditions
import IMLTT.proofs.admissable.Contexts

/- # Definitional Equality is Equivalence Relation -/

#check HasType.recOn

theorem defeq_term_refl : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsEqualType Γ A A)
      (motive_3 := fun Γ a A _haA => IsEqualTerm Γ a a A)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      haA
    · apply IsCtx.empty
    · intro n Γ A hiC hA _ _
      apply IsCtx.extend hiC hA
    · intro n Γ hiC _
      apply IsEqualType.unit_form_eq hiC
    · intro n Γ hiC _
      apply IsEqualType.empty_form_eq hiC
    · intro n Γ A B _hA _hB ihA ihB
      apply IsEqualType.pi_form_eq ihA ihB
    · intro n Γ A B _hA _hB ihA ihB
      apply IsEqualType.sigma_form_eq ihA ihB
    · intro n Γ a A a' _haA _haA' ihaA ihaA'
      apply IsEqualType.iden_form_eq ihaA ihaA'
    · intro n Γ hiC _
      apply IsEqualType.univ_form_eq hiC
    · intro n Γ A _hAU ihAU
      apply IsEqualType.univ_elim_eq ihAU
    · intro n Γ A hA _
      apply IsEqualTerm.var_eq hA
    · intro n Γ hiC _
      apply IsEqualTerm.unit_intro_eq hiC
    · intro n Γ A b B _hbB ihbB
      apply IsEqualTerm.pi_intro_eq ihbB
    · intro n Γ a A b B _haA _hbB ihaA ihbB
      apply IsEqualTerm.sigma_intro_eq ihaA ihbB
    · intro n Γ a A _haA ihaA
      apply IsEqualTerm.iden_intro_eq sorry ihaA
    · intro n Γ hiC _
      apply IsEqualTerm.univ_unit_eq hiC
    · intro n Γ hiC _
      apply IsEqualTerm.univ_empty_eq hiC
    · intro n Γ A B _hAU _hBU ihAU ihBU
      apply IsEqualTerm.univ_pi_eq ihAU ihBU
    · intro n Γ A B _hAU _hBU ihAU ihBU
      apply IsEqualTerm.univ_sigma_eq ihAU ihBU
    · intro n Γ A a a' _hAU _haA _haA' ihAU ihaA ihaA'
      apply IsEqualTerm.univ_iden_eq ihAU ihaA ihaA'
    · intro n Γ A a b _hA _haA _hb1 ihA ihaA ihb1
      apply IsEqualTerm.unit_elim_eq ihA ihaA ihb1
    · intro n Γ A b _hA _hb0 ihA ihb0
      apply IsEqualTerm.empty_elim_eq ihA ihb0
    · intro n Γ f A B a _hfPi _haA ihfPi ihaA
      apply IsEqualTerm.pi_elim_eq ihfPi ihaA
    · intro n Γ p A B C c _hpSi _hC _hcC ihpSi ihC ihcC
      apply IsEqualTerm.sigma_elim_eq
      · apply ihpSi
      · apply ihC
      · apply ihcC
    · intro n Γ A B b p a a' _hB _hbB _hpId ihB ihbB ihpId
      apply IsEqualTerm.iden_elim_eq ihB ihbB sorry ihpId
    · intro n Γ a A B _haA _hAB ihaA ihAB
      apply IsEqualTerm.ty_conv_eq ihaA ihAB
    · intro n Γ hiC _
      apply IsEqualType.unit_form_eq hiC
    · intro n Γ hiC _
      apply IsEqualType.empty_form_eq hiC
    · intro n Γ A A' B B' hAA hBB _ _
      apply IsEqualType.pi_form_eq hAA hBB
    · intro n Γ A A' B B' hAA hBB _ _
      apply IsEqualType.sigma_form_eq hAA hBB
    · intro n Γ a₁ a₂ A a₃ a₄ haaA haaA' _ _
      apply IsEqualType.iden_form_eq haaA haaA'
    · intro n Γ hiC _
      apply IsEqualType.univ_form_eq hiC
    · intro n Γ A A' hAAU _
      apply IsEqualType.univ_elim_eq hAAU
    · intro n Γ A hA _
      apply IsEqualTerm.var_eq hA
    · intro n Γ A a hA haA _ _
      apply IsEqualTerm.unit_comp hA haA
    · intro n Γ A b B a hbB haA _ _
      apply IsEqualTerm.pi_comp hbB haA
    · intro n Γ a A b B C c haA hbB hC hcC _ _ _ _
      apply IsEqualTerm.sigma_comp haA hbB hC hcC
    · intro n Γ A B b a hB hbB haA _ _ _
      apply IsEqualTerm.iden_comp hB hbB haA
    · intro n Γ hiC _
      apply IsEqualTerm.unit_intro_eq hiC
    · intro n Γ A A' a a' b b' hAA haaA hbb1 _ _ _
      apply IsEqualTerm.unit_elim_eq hAA haaA hbb1
    · intro n Γ A A' b b' hAA hbb0 _ _
      apply IsEqualTerm.empty_elim_eq hAA hbb0
    · intro n Γ A b b' B A' hbbB _
      apply IsEqualTerm.pi_intro_eq hbbB
    · intro n Γ f f' A B a a' hffPi haaA _ _
      apply IsEqualTerm.pi_elim_eq hffPi haaA
    · intro n Γ a a' A b b' B haaA hbbB _ _ 
      apply IsEqualTerm.sigma_intro_eq haaA hbbB
    · intro n Γ A B p p' C C' c c' hppSi hCC hccC _ _ _
      apply IsEqualTerm.sigma_elim_eq hppSi hCC hccC
    · intro n Γ a a' A A' hAA haaA _ _
      apply IsEqualTerm.iden_intro_eq hAA haaA
    · intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hIdId hppId _ _ _ _
      apply IsEqualTerm.iden_elim_eq hBB hbbB hIdId hppId
    · intro n Γ hiC _
      apply IsEqualTerm.univ_unit_eq hiC
    · intro n Γ hiC _
      apply IsEqualTerm.univ_empty_eq hiC
    · intro n Γ A A' B B' hAAU hBBU _ _
      apply IsEqualTerm.univ_pi_eq hAAU hBBU
    · intro n Γ A A' B B' hAAU hBBU _ _
      apply IsEqualTerm.univ_sigma_eq hAAU hBBU
    · intro n Γ A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' _ _ _
      apply IsEqualTerm.univ_iden_eq hAAU haaA haaA'
    · intro n Γ a b A B habA hAB _ _
      apply IsEqualTerm.ty_conv_eq habA hAB

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
    | .pi_intro_eq hbbB => sorry
    | .pi_elim_eq haaA hffPi => sorry
    | .sigma_intro_eq haaA hbbB => sorry
    | .sigma_elim_eq hppSi hCC hccC => sorry
    | .iden_intro_eq hAA haaA  => sorry
    | .iden_elim_eq hBB hbbB hIdId hppId => sorry
    | .univ_unit_eq hiC => sorry
    | .univ_empty_eq hiC => sorry
    | .univ_pi_eq hAAU hBBU => sorry
    | .univ_sigma_eq hAAU hBBU => sorry
    | .univ_iden_eq hAAU haaA haaA' => sorry
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
