import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import Aesop

theorem boundary_type_term_a :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, (Γ ⊢ A type) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, (Γ ⊢ A ≡ A' type) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ∶ A) ∧ Γ ⊢ A type) :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => IsType Γ A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A)
      (motive_5 := fun Γ a a' A _haaA => HasType Γ a A ∧ IsType Γ A)
    case HasTypeVar =>
      intro n Γ A S hA hEq _ihA
      rw [hEq]
      apply weakening_type hA hA
    case HasTypePiIntro =>
      intro n Γ A b B _hbB ihbB
      apply IsType.pi_form
      · have hiCA := boundary_ctx_type ihbB
        apply ctx_extr hiCA
      · apply ihbB
    case HasTypeSigmaIntro =>
      intro n Γ a A b B haA _hbB ihaA ihbB
      apply IsType.sigma_form
      · apply ihaA
      · apply substitution_inv_type
        · rfl
        · apply ihbB
        · apply haA
    case HasTypeUnitElim =>
      intro n Γ A a b S hA _haA hb1 hEq _ihA _ihaA _ihb1
      rw [hEq]
      apply substitution_type
      · apply hb1
      · apply hA
    case HasTypeEmptyElim =>
      intro n Γ A b S hA hb0 hEq _ihA _ihb0
      rw [hEq]
      apply substitution_type
      · apply hb0
      · apply hA
    case HasTypePiElim =>
      intro n Γ f A B a S _hfPi haA hEq ihfPi _ihaA
      rw [hEq]
      apply substitution_type
      · apply haA
      · apply And.right (pi_is_type_inversion ihfPi)
    case HasTypeSigmaElim =>
      intro n Γ A B p C c S hpSi _hC _hcC hEq _ihpSi ihC _ihcC
      rw [hEq]
      apply substitution_type
      · apply hpSi
      · apply ihC
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p S hB _hbB hpId hB' hEq _ihB ihbB ihB' ihpId
      rw [hEq]
      apply hB'
    case HasTypeTyConv =>
      intro n Γ a A B _haA hAB _ihaA _ihAB
      sorry
    case IsEqualTypeIdenFormEq =>
      intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA'
      apply IsType.iden_form
      · apply And.left ihaaA
      · apply HasType.ty_conv (And.left ihaaA') (sorry)
    case IsEqualTypeUnivElimEq =>
      intro n Γ A A' hAAU ihAAU
      apply IsType.univ_elim (And.left ihAAU)
    case IsEqualTermVarEq =>
      intro n Γ A S hA hEq _ihA
      rw [hEq]
      apply And.intro
      · apply HasType.var hA rfl
      · apply weakening_type hA hA
    case IsEqualTermUnitComp =>
      intro n Γ A a S hA haA hEq ihA ihaA
      rw [hEq]
      apply And.intro
      · apply HasType.unit_elim
        · apply hA
        · apply haA
        · apply HasType.unit_intro (boundary_ctx_term haA)
        · rfl
      · apply ihaA
    case IsEqualTermPiComp =>
      intro n Γ A b B a S S' _hbB haA hEq hEq' ihbB _ihaA
      rw [hEq']
      apply And.intro
      · apply HasType.pi_elim
        · apply HasType.pi_intro _hbB
        · apply haA
        · rfl
      · apply substitution_type
        · apply haA
        · apply ihbB
    case IsEqualTermSigmaComp =>
      intro n Γ a A b B C s S c haA hbB hC _hcC hEqs hEqS _ihaA _ihbB _ihC _ihcC
      rw [hEqS]
      apply And.intro
      · apply HasType.sigma_elim
        · apply HasType.sigma_intro
          · apply haA
          · apply hbB
        · apply _ihC
        · apply _hcC
        · rfl
      · apply substitution_type
        · apply HasType.sigma_intro haA hbB
        · apply hC
    case IsEqualTermIdenComp =>
      intro n Γ A B b a S _hB _hbB _haA hB' hEq _ihB ihbB _ihaA ihB'
      rw [hEq]
      apply And.intro
      · apply HasType.iden_elim
        · apply _hB
        · apply _hbB
        · apply HasType.iden_intro _haA
        · apply ihbB
        · rfl
      · apply ihbB
    case IsEqualTermUnitElimEq =>
      intro n Γ A A' a a' b b' S _hAA _haaA hbb1 hEq ihAA _ihaaA _ihb1
      rw [hEq]
      apply And.intro
      · apply HasType.unit_elim
        · apply ihAA
        · apply And.left _ihaaA
        · apply And.left _ihb1
        · rfl
      · apply substitution_type
        · apply And.left _ihb1
        · apply ihAA
    case IsEqualTermEmptyElimEq =>
      intro n Γ A A' b b' S _hAA hbb0 hEq ihAA _ihb0
      rw [hEq]
      apply And.intro
      · apply HasType.empty_elim
        · apply ihAA
        · apply And.left _ihb0
        · rfl
      · apply substitution_type
        · apply And.left _ihb0
        · apply ihAA
    case IsEqualTermPiIntroEq =>
      intro n Γ A b b' B B' A' _hbbB hPiPi ihbbB ihPipi
      apply And.intro
      · apply HasType.pi_intro (And.left ihbbB)
      · apply IsType.pi_form
        · have hiCA := boundary_ctx_term_eq _hbbB
          apply ctx_extr hiCA
        · apply And.right ihbbB
    case IsEqualTermPiElimEq =>
      intro n Γ f f' A B a a' S _hffPi haaA hEq ihffPi _ihaaA
      rw [hEq]
      apply And.intro
      · apply HasType.pi_elim
        · apply And.left ihffPi
        · apply And.left _ihaaA
        · rfl
      · apply substitution_type
        · apply And.left _ihaaA
        · apply And.right (pi_is_type_inversion (And.right ihffPi))
    case IsEqualTermSigmaIntroEq =>
      intro n Γ a a' A b b' B haaA _hbbB ihaaA ihbbB
      apply And.intro
      · apply HasType.sigma_intro
        · apply And.left ihaaA
        · apply And.left ihbbB
      · apply IsType.sigma_form
        · apply And.right ihaaA
        · apply substitution_inv_type
          · rfl
          · apply And.right ihbbB
          · apply And.left ihaaA
    case IsEqualTermSigmaElimEq =>
      intro n Γ A B A' B' p p' C C' c c' S _hSiSi hppSi _hCC _hccC hEq _ihSiSi _ihppSi ihCC _ihccC
      rw [hEq]
      apply And.intro
      · apply HasType.sigma_elim
        · apply And.left _ihppSi
        · apply ihCC
        · apply And.left _ihccC
        · rfl
      · apply substitution_type
        · apply And.left _ihppSi
        · apply ihCC
    case IsEqualTermIdenIntroEq =>
      intro n Γ A A' a a' _hAA haaA ihAA _ihaA
      apply And.intro
      · apply HasType.iden_intro (And.left _ihaA)
      · have haA := And.left _ihaA
        apply IsType.iden_form haA haA
    case IsEqualTermIdenElimEq =>
      intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' S
      intro _hBB _hbbB _hIdId _hppId hBB' hEq _ihBB ihbbB _ihIdId _ihppId ihBB'
      rw [hEq]
      apply And.intro
      · apply HasType.iden_elim
        · apply _ihBB
        · apply And.left ihbbB
        · apply And.left _ihppId
        · apply ihBB'
        · rfl
      · apply ihBB'
    case IsEqualTermTyConvEq =>
      intro n Γ a b A B habA hAB ihabA ihA
      apply And.intro
      · apply HasType.ty_conv
        · apply And.left ihabA
        · apply hAB
      · sorry
    any_goals sorry -- aesop

theorem boundary_type_term :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, (Γ ⊢ A type) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, (Γ ⊢ A ≡ A' type) → Γ ⊢ A type ∧ Γ ⊢ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type) :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => IsType Γ A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A ∧ IsType Γ A')
      (motive_5 := fun Γ a a' A _haaA => HasType Γ a A ∧ HasType Γ a' A ∧ IsType Γ A)
    case HasTypeVar =>
      intro n Γ A S hA hEq _ihA
      rw [hEq]
      apply weakening_type hA hA
    case HasTypePiIntro =>
      intro n Γ A b B _hbB ihbB
      apply IsType.pi_form
      · have hiCA := boundary_ctx_type ihbB
        apply ctx_extr hiCA
      · apply ihbB
    case HasTypeSigmaIntro =>
      intro n Γ a A b B haA _hbB ihaA ihbB
      apply IsType.sigma_form
      · apply ihaA
      · apply substitution_inv_type
        · rfl
        · apply ihbB
        · apply haA
    case HasTypeUnitElim =>
      intro n Γ A a b S hA _haA hb1 hEq _ihA _ihaA _ihb1
      rw [hEq]
      apply substitution_type
      · apply hb1
      · apply hA
    case HasTypeEmptyElim =>
      intro n Γ A b S hA hb0 hEq _ihA _ihb0
      rw [hEq]
      apply substitution_type
      · apply hb0
      · apply hA
    case HasTypePiElim =>
      intro n Γ f A B a S _hfPi haA hEq ihfPi _ihaA
      rw [hEq]
      apply substitution_type
      · apply haA
      · apply And.right (pi_is_type_inversion ihfPi)
    case HasTypeSigmaElim =>
      intro n Γ A B p C c S hpSi _hC _hcC hEq _ihpSi ihC _ihcC
      rw [hEq]
      apply substitution_type
      · apply hpSi
      · apply ihC
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p S hB _hbB hpId hB' hEq _ihB ihbB ihB' ihpId
      rw [hEq]
      apply hB'
    case HasTypeTyConv =>
      intro n Γ a A B _haA hAB _ihaA _ihAB
      apply And.right _ihAB
    case IsEqualTypeIdenFormEq =>
      intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA'
      apply And.intro
      · apply IsType.iden_form
        · apply And.left ihaaA
        · apply HasType.ty_conv_symm (And.left ihaaA') (hAA)
      · apply IsType.iden_form
        · apply HasType.ty_conv (And.left (And.right ihaaA)) hAA
        · apply And.left (And.right ihaaA')
    case IsEqualTypeUnivElimEq =>
      intro n Γ A A' hAAU ihAAU
      apply And.intro
      · apply IsType.univ_elim (And.left ihAAU)
      · apply IsType.univ_elim (And.left (And.right ihAAU))
    case IsEqualTermVarEq =>
      intro n Γ A S hA hEq _ihA
      rw [hEq]
      apply And.intro
      · apply HasType.var hA rfl
      · apply And.intro
        · apply HasType.var hA rfl
        · apply weakening_type hA hA
    case IsEqualTermUnitComp =>
      intro n Γ A a S hA haA hEq ihA ihaA
      rw [hEq]
      apply And.intro
      · apply HasType.unit_elim
        · apply hA
        · apply haA
        · apply HasType.unit_intro (boundary_ctx_term haA)
        · rfl
      · apply And.intro
        · apply haA
        · apply ihaA
    case IsEqualTermPiComp =>
      intro n Γ A b B a S S' _hbB haA hEq hEq' ihbB _ihaA
      rw [hEq']
      apply And.intro
      · apply HasType.pi_elim
        · apply HasType.pi_intro _hbB
        · apply haA
        · rfl
      · apply And.intro
        · rw [hEq]
          apply substitution_term
          · apply haA
          · apply _hbB
        · apply substitution_type
          · apply haA
          · apply ihbB
    case IsEqualTermSigmaComp =>
      intro n Γ a A b B C s S c haA hbB hC _hcC hEqs hEqS _ihaA _ihbB _ihC _ihcC
      rw [hEqS]
      apply And.intro
      · apply HasType.sigma_elim
        · apply HasType.sigma_intro
          · apply haA
          · apply hbB
        · apply _ihC
        · apply _hcC
        · rfl
      · apply And.intro
        · rw [hEqs]
          rw [substitution_separate_test_a]
          sorry
          -- apply substitution_term -- substituon_term regel anpassen mit 'trick' s = ...
        · apply substitution_type
          · apply HasType.sigma_intro haA hbB
          · apply hC
    case IsEqualTermIdenComp =>
      intro n Γ A B b a S _hB _hbB _haA hB' hEq _ihB ihbB _ihaA ihB'
      rw [hEq]
      apply And.intro
      · apply HasType.iden_elim
        · apply _hB
        · apply _hbB
        · apply HasType.iden_intro _haA
        · apply ihbB
        · rfl
      · apply And.intro
        · apply _hbB
        · apply ihbB
    case IsEqualTermUnitElimEq =>
      intro n Γ A A' a a' b b' S _hAA _haaA hbb1 hEq ihAA _ihaaA _ihb1
      rw [hEq]
      apply And.intro
      · apply HasType.unit_elim
        · apply And.left ihAA
        · apply And.left _ihaaA
        · apply And.left _ihb1
        · rfl
      · have hAA' := substitution_type_eq (And.left (And.right _ihb1)) (_hAA)
        apply And.intro
        · apply HasType.ty_conv
          · apply HasType.unit_elim
            · apply And.right ihAA
            · sorry
            · apply And.left (And.right _ihb1)
            · rfl
          · sorry
        · apply substitution_type
          · apply And.left _ihb1
          · apply And.left ihAA
    case IsEqualTermEmptyElimEq =>
      intro n Γ A A' b b' S _hAA hbb0 hEq ihAA _ihb0
      rw [hEq]
      apply And.intro
      · apply HasType.empty_elim
        · apply And.left ihAA
        · apply And.left _ihb0
        · rfl
      · apply And.intro
        · apply HasType.empty_elim
          · sorry -- apply And.right ihAA
          · sorry -- apply And.left (And.right _ihb0)
          · sorry
        · apply substitution_type
          · apply And.left _ihb0
          · apply And.left ihAA
    case IsEqualTermPiIntroEq =>
      intro n Γ A b b' B B' A' _hbbB hPiPi ihbbB ihPipi
      apply And.intro
      · apply HasType.pi_intro (And.left ihbbB)
      · apply And.intro
        · sorry
        · apply IsType.pi_form
          · have hiCA := boundary_ctx_term_eq _hbbB
            apply ctx_extr hiCA
          · apply And.right (And.right ihbbB)
    case IsEqualTermPiElimEq =>
      intro n Γ f f' A B a a' S _hffPi haaA hEq ihffPi _ihaaA
      rw [hEq]
      apply And.intro
      · apply HasType.pi_elim
        · apply And.left ihffPi
        · apply And.left _ihaaA
        · rfl
      · apply And.intro
        · sorry
        · apply substitution_type
          · apply And.left _ihaaA
          · apply And.right (pi_is_type_inversion (And.right (And.right ihffPi)))
    case IsEqualTermSigmaIntroEq =>
      intro n Γ a a' A b b' B haaA _hbbB ihaaA ihbbB
      apply And.intro
      · apply HasType.sigma_intro
        · apply And.left ihaaA
        · apply And.left ihbbB
      · apply And.intro
        · sorry
        · apply IsType.sigma_form
          · apply And.right (And.right ihaaA)
          · apply substitution_inv_type
            · rfl
            · apply And.right (And.right ihbbB)
            · apply And.left ihaaA
    case IsEqualTermSigmaElimEq =>
      intro n Γ A B A' B' p p' C C' c c' S _hSiSi hppSi _hCC _hccC hEq _ihSiSi _ihppSi ihCC _ihccC
      rw [hEq]
      apply And.intro
      · apply HasType.sigma_elim
        · apply And.left _ihppSi
        · apply And.left ihCC
        · apply And.left _ihccC
        · rfl
      · apply And.intro
        · sorry
        · apply substitution_type
          · apply And.left _ihppSi
          · apply And.left ihCC
    case IsEqualTermIdenIntroEq =>
      intro n Γ A A' a a' _hAA haaA ihAA _ihaA
      apply And.intro
      · apply HasType.iden_intro (And.left _ihaA)
      · have haA := And.left _ihaA
        apply And.intro
        · sorry
        · apply IsType.iden_form haA haA
    case IsEqualTermIdenElimEq =>
      intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' S
      intro _hBB _hbbB _hIdId _hppId hBB' hEq _ihBB ihbbB _ihIdId _ihppId ihBB'
      rw [hEq]
      apply And.intro
      · apply HasType.iden_elim
        · apply And.left _ihBB
        · apply And.left ihbbB
        · apply And.left _ihppId
        · apply And.left ihBB'
        · rfl
      · apply And.intro
        · sorry
        · apply And.left ihBB'
    case IsEqualTermTyConvEq =>
      intro n Γ a b A B habA hAB ihabA ihA
      apply And.intro
      · apply HasType.ty_conv
        · apply And.left ihabA
        · apply hAB
      · apply And.intro
        · apply HasType.ty_conv (And.left (And.right ihabA)) hAB
        · apply And.right ihA
    case IsEqualTermTyConvEqSymm =>
      intro n Γ a b A B habA hAB ihabA ihA
      apply And.intro
      · apply HasType.ty_conv_symm
        · apply And.left ihabA
        · apply hAB
      · apply And.intro
        · apply HasType.ty_conv_symm (And.left (And.right ihabA)) hAB
        · apply And.left ihA
    any_goals sorry -- aesop
