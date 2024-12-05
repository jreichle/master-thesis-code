import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.boundary.BoundaryIsCtx
import IMLTT.proofs.admissable.Contexts

import IMLTT.proofs.Recursor

import aesop

/- # Definitional Equality is Equivalence Relation -/

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ a ≡ a ∶ A) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A)
  :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsEqualType Γ A A)
      (motive_3 := fun Γ a A _haA => IsEqualTerm Γ a a A)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
    case IsTypeIdenForm =>
      intro n Γ a A a' hA haA haA' ihA haaA haaA'
      apply IsEqualType.iden_form_eq
      · apply ihA
      · apply haaA
      · apply haaA'
    any_goals aesop

theorem defeq_term_refl : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    apply (And.left (And.right (And.right defeq_refl)))
    apply haA


theorem defeq_type_refl : IsType Γ A → IsEqualType Γ A A :=
  by
    intro hA
    apply (And.left (And.right defeq_refl))
    apply hA

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
    | .sigma_elim_eq hSiSi hppSi hCC hccC => sorry
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
    | .iden_form_eq hAA haaA haaA' =>
      by
        apply IsEqualType.iden_form_eq
        · apply defeq_type_symm hAA
        · apply IsEqualTerm.ty_conv_eq (defeq_term_symm haaA) hAA
        · apply IsEqualTerm.ty_conv_eq (defeq_term_symm haaA') (defeq_type_symm hAA)
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
    | .iden_form_eq hAA haaA haaA' =>
      by
        sorry
    | .univ_form_eq hic =>
      by
        apply hBC
    | .univ_elim_eq hAAU =>
      by
        sorry
