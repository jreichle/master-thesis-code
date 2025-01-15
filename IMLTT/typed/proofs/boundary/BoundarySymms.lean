import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem boundary_has_type :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, (Γ ⊢ A type) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ a ∶ A) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, (Γ ⊢ A ≡ A' type) → Γ ⊢ A type ∧ Γ ⊢ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ∶ A) ∧ Γ ⊢ a' ∶ A) :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => HasType Γ a A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A ∧ IsType Γ A')
      (motive_5 := fun Γ a a' A _haaA => HasType Γ a A ∧ HasType Γ a' A)
    case IsEqualTypeIdenFormEq =>
      intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA'
      apply And.intro
      · apply IsType.iden_form
        · apply And.left ihaaA
        · apply HasType.ty_conv (And.left ihaaA') (IsEqualType.symm hAA)
      · apply IsType.iden_form
        · apply HasType.ty_conv (And.right ihaaA) hAA
        · apply (And.right ihaaA')
    case IsEqualTypeUnivElimEq =>
      intro n Γ A A' hAAU ihAAU
      apply And.intro
      · apply IsType.univ_elim (And.left ihAAU)
      · apply IsType.univ_elim (And.right ihAAU)
    case IsEqualTermVarEq =>
      intro n Γ A S hA hEq _ihA
      rw [hEq]
      apply And.intro
      · apply HasType.var hA rfl
      · apply HasType.var hA rfl
    case IsEqualTermUnitComp =>
      intro n Γ A a S hA haA hEq ihA ihaA
      rw [hEq]
      apply And.intro
      · apply HasType.unit_elim
        · apply hA
        · apply haA
        · apply HasType.unit_intro (boundary_ctx_term haA)
        · rfl
      · apply haA
    case IsEqualTermPiComp =>
      intro n Γ A b B a S S' _hbB haA hEq hEq' ihbB _ihaA
      rw [hEq']
      apply And.intro
      · apply HasType.pi_elim
        · apply HasType.pi_intro _hbB
        · apply haA
        · rfl
      · rw [hEq]
        apply substitution_term
        · apply haA
        · apply _hbB
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
      · rw [hEqs]
        sorry
    case IsEqualTermIdenComp =>
      intro n Γ A B b a S _hB _hbB _haA hB' hEq _ihB ihbB _ihaA ihB'
      rw [hEq]
      apply And.intro
      · apply HasType.iden_elim
        · apply _hB
        · apply _hbB
        · apply HasType.iden_intro _haA
        · apply ihB'
        · rfl
      · apply _hbB
    case IsEqualTermUnitElimEq =>
      intro n Γ A A' a a' b b' S _hAA _haaA hbb1 hEq ihAA _ihaaA _ihb1
      rw [hEq]
      apply And.intro
      · apply HasType.unit_elim
        · apply And.left ihAA
        · apply And.left _ihaaA
        · apply And.left _ihb1
        · rfl
      · have hAA' := substitution_type_eq (And.right _ihb1) (_hAA)
        apply HasType.ty_conv
        · apply HasType.unit_elim
          · apply And.right ihAA
          · sorry
          · apply And.right _ihb1
          · rfl
        · sorry
    case IsEqualTermEmptyElimEq =>
      intro n Γ A A' b b' S _hAA hbb0 hEq ihAA _ihb0
      rw [hEq]
      apply And.intro
      · apply HasType.empty_elim
        · apply And.left ihAA
        · apply And.left _ihb0
        · rfl
      · apply HasType.empty_elim
        · sorry -- apply And.right ihAA
        · sorry -- apply And.left (And.right _ihb0)
        · sorry
    case IsEqualTermPiIntroEq =>
      intro n Γ A b b' B B' A' _hbbB hPiPi ihbbB ihPipi
      apply And.intro
      · apply HasType.pi_intro (And.left ihbbB)
      · constructor
        · sorry
        · sorry
        · sorry
    case IsEqualTermPiElimEq =>
      intro n Γ f f' A B a a' S _hffPi haaA hEq ihffPi _ihaaA
      rw [hEq]
      apply And.intro
      · apply HasType.pi_elim
        · apply And.left ihffPi
        · apply And.left _ihaaA
        · rfl
      · sorry
    case IsEqualTermSigmaIntroEq =>
      intro n Γ a a' A b b' B haaA _hbbB ihaaA ihbbB
      apply And.intro
      · apply HasType.sigma_intro
        · apply And.left ihaaA
        · apply And.left ihbbB
      · sorry
    case IsEqualTermSigmaElimEq =>
      intro n Γ A B A' B' p p' C C' c c' S _hSiSi hppSi _hCC _hccC hEq _ihSiSi _ihppSi ihCC _ihccC
      rw [hEq]
      apply And.intro
      · apply HasType.sigma_elim
        · apply And.left _ihppSi
        · apply And.left ihCC
        · apply And.left _ihccC
        · rfl
      · sorry
    case IsEqualTermIdenIntroEq =>
      intro n Γ A A' a a' _hAA haaA ihAA _ihaA
      apply And.intro
      · apply HasType.iden_intro (And.left _ihaA)
      · have haA := And.left _ihaA
        sorry
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
      · sorry
    case IsEqualTermTyConvEq =>
      intro n Γ a b A B habA hAB ihabA ihA
      apply And.intro
      · apply HasType.ty_conv
        · apply And.left ihabA
        · apply hAB
      · apply HasType.ty_conv (And.right ihabA) hAB
    any_goals sorry -- aesop
