import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.boundary.BoundaryHasType

set_option diagnostics true
set_option maxHeartbeats 1000000

theorem boundary_type :
  (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ A type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ A type)
  :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => IsType Γ A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A)
      (motive_5 := fun Γ a a' A _haaA => IsType Γ A)
    case HasTypeVar =>
      intro n Γ A hA _ihA
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
      intro n Γ A a b hA _haA hb1 _ihA _ihaA _ihb1
      apply substitution_type
      · apply hb1
      · apply hA
    case HasTypeEmptyElim =>
      intro n Γ A b hA hb0 _ihA _ihb0
      apply substitution_type
      · apply hb0
      · apply hA
    case HasTypePiElim =>
      intro n Γ f A B a _hfPi haA ihfPi _ihaA
      apply substitution_type
      · apply haA
      · apply And.right (pi_is_type_inversion ihfPi)
    case HasTypeSigmaElim =>
      intro n Γ A B p C c hpSi _hC _hcC _ihpSi ihC _ihcC
      apply substitution_type
      · apply hpSi
      · apply ihC
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p hB _hbB hpId hB' _ihB ihbB ihpId ihB'
      apply hB'
    case HasTypeTyConv =>
      intro n Γ a A B _haA hAB _ihaA _ihAB
      sorry -- apply boundary_is_type_type_eq' hAB
    case IsEqualTypeIdenFormEq =>
      intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA'
      have haA := boundary_has_type_term_eq haaA
      have haA' := boundary_has_type_term_eq haaA'
      apply IsType.iden_form 
      · apply haA
      · apply HasType.ty_conv_symm haA' hAA
    case IsEqualTypeUnivElimEq =>
      intro n Γ A A' hAAU _hU
      have hAU := boundary_has_type_term_eq hAAU
      apply IsType.univ_elim hAU
    case IsEqualTermVarEq =>
      intro n Γ A hA _ihA
      apply weakening_type hA hA
    case IsEqualTermPiComp =>
      intro n Γ A b B a _hbB haA ihbB _ihaA
      apply substitution_type
      · apply haA
      · apply ihbB
    case IsEqualTermSigmaComp =>
      intro n Γ a A b B C c haA hbB hC _hcC _ihaA _ihbB _ihC _ihcC
      apply substitution_type
      · apply HasType.sigma_intro haA hbB
      · apply hC
    case IsEqualTermIdenComp =>
      intro n Γ A B b a _hB _hbB _haA hB' _ihB ihbB _ihaA ihB'
      apply ihbB
    case IsEqualTermUnitElimEq =>
      intro n Γ A A' a a' b b' _hAA _haaA hbb1 ihAA _ihaaA _ihb1
      apply substitution_type
      · apply boundary_has_type_term_eq hbb1
      · apply ihAA
    case IsEqualTermEmptyElimEq =>
      intro n Γ A A' b b' _hAA hbb0 ihAA _ihb0
      apply substitution_type
      · apply boundary_has_type_term_eq hbb0
      · apply ihAA
    case IsEqualTermPiIntroEq =>
      intro n Γ A A' b b' B B' _hbbB hPiPi ihbbB ihPiPi
      apply IsType.pi_form
      · have hiCA := boundary_ctx_type ihbbB
        apply ctx_extr hiCA
      · apply ihbbB
    case IsEqualTermPiElimEq =>
      intro n Γ f f' A B a a' _hffPi haaA ihffPi _ihaaA
      apply substitution_type
      · apply boundary_has_type_term_eq haaA
      · apply And.right (pi_is_type_inversion ihffPi)
    case IsEqualTermSigmaIntroEq =>
      intro n Γ a a' A b b' B haaA _hbbB ihaaA ihbbB
      apply IsType.sigma_form
      · apply ihaaA
      · apply substitution_inv_type
        · rfl
        · apply ihbbB
        · apply boundary_has_type_term_eq haaA
    case IsEqualTermSigmaElimEq =>
      intro n Γ A B A' B' p p' C C' c c' _hSiSi hppSi _hCC _hccC _ihSiSi _ihppSi ihCC _ihccC
      apply substitution_type
      · apply boundary_has_type_term_eq hppSi
      · apply ihCC
    case IsEqualTermIdenIntroEq =>
      intro n Γ A A' a a' _hAA haaA ihAA _ihaA
      have haA := boundary_has_type_term_eq haaA
      apply IsType.iden_form haA haA
    case IsEqualTermIdenElimEq =>
      intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p'
      intro _hBB _hbbB _hIdId _hppId hB' _ihBB ihbbB _ihIdId _ihppId ihB'
      apply hB'
    case IsEqualTermTyConvEq =>
      intro n Γ a b A B habA hAB ihabA ihA
      sorry -- apply defeq_is_type' hAB
    any_goals aesop

-- theorem boundary_is_type_term {n : Nat} {Γ : Ctx n} {s S : Tm n} :
--     (Γ ⊢ s ∶ S) → Γ ⊢ S type := 
--   by
--     sorry
-- 
-- theorem boundary_is_type_term_eq {n : Nat} {Γ : Ctx n} {s s' S : Tm n} :
--     (Γ ⊢ s ≡ s' ∶ S) → Γ ⊢ S type :=
--   by
--     intro hssS
--     have hsS := boundary_has_type_term_eq hssS
--     apply boundary_is_type_term hsS
