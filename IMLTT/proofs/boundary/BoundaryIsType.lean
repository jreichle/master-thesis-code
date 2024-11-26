import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.admissable.Inversion
import IMLTT.proofs.admissable.Weakening
import IMLTT.proofs.admissable.Substitution
import IMLTT.proofs.boundary.BoundaryIsCtx
import IMLTT.proofs.boundary.BoundaryHasType

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
      intro n Γ A hA ihA
      apply weakening_type hA hA
    case HasTypePiIntro =>
      intro n Γ A b B hbB ihbB
      apply IsType.pi_form 
      · have hiCA := boundary_ctx_type ihbB
        apply ctx_extr hiCA
      · apply ihbB
    case HasTypeSigmaIntro =>
      intro n Γ a A b B haA hbB ihaA ihbB
      apply IsType.sigma_form
      · apply ihaA
      · apply substitution_inv_type
        · rfl
        · apply ihbB
        · apply haA
    case HasTypeUnitElim =>
      intro n Γ A a b hA haA hb1 ihA ihaA ihb1
      apply substitution_type
      · apply hb1
      · apply hA
    case HasTypeEmptyElim =>
      intro n Γ A b hA hb0 ihA ihb0
      apply substitution_type
      · apply hb0
      · apply hA
    case HasTypePiElim =>
      intro n Γ f A B a hfPi haA ihfPi ihaA
      apply substitution_type
      · apply haA
      · apply And.right (pi_is_type_inversion ihfPi)
    case HasTypeSigmaElim =>
      intro n Γ A B p C c hSi hpSi hC hcC ihSi ihpSi ihC ihcC
      apply substitution_type
      · apply hpSi
      · apply ihC
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p hB hbB hIden hpIden ihB ihbB ihIden ihpIden
      rw [substitution_zero_n] -- rewrite to substitution_zero x 4subs
      apply substitution_type
      · sorry
      · sorry
    case HasTypeTyConv =>
      intro n Γ a A B haA hAB ihaA ihAB
      sorry
    case IsEqualTypeIdenFormEq =>
      intro n Γ a₁ a₂ A a₃ a₄ haaA haaA' ihaaA ihaaA'
      have haA := boundary_has_type haaA
      have haA' := boundary_has_type haaA'
      apply IsType.iden_form haA haA'
    case IsEqualTypeUnivElimEq =>
      intro n Γ A A' hAAU hU
      have hAU := boundary_has_type hAAU
      apply IsType.univ_elim hAU
    case IsEqualTermVarEq =>
      intro n Γ A hA ihA
      apply weakening_type hA hA
    case IsEqualTermPiComp =>
      intro n Γ A b B a hbB haA ihbB ihaA
      apply substitution_type
      · apply haA
      · apply ihbB
    case IsEqualTermSigmaComp =>
      intro n Γ a A b B C c haA hbB hC hcC ihaA ihbB ihC ihcC
      apply substitution_type
      · apply HasType.sigma_intro haA hbB
      · apply hC
    case IsEqualTermIdenComp =>
      intro n Γ A B b a hB hbB haA ihB ihbB ihaA
      sorry
    case IsEqualTermUnitElimEq =>
      intro n Γ A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihb1
      apply substitution_type
      · apply boundary_has_type hbb1
      · apply ihAA
    case IsEqualTermEmptyElimEq =>
      intro n Γ A A' b b' hAA hbb0 ihAA ihb0
      apply substitution_type
      · apply boundary_has_type hbb0
      · apply ihAA
    case IsEqualTermPiIntroEq =>
      intro n Γ A b b' B A' hbbB ihbbB
      apply IsType.pi_form
      · have hiCA := boundary_ctx_type ihbbB
        apply ctx_extr hiCA
      · apply ihbbB
    case IsEqualTermPiElimEq =>
      intro n Γ f f' A B a a' hffPi haaA ihffPi ihaaA
      apply substitution_type
      · apply boundary_has_type haaA
      · apply And.right (pi_is_type_inversion ihffPi)
    case IsEqualTermSigmaIntroEq =>
      intro n Γ a a' A b b' B haaA hbbB ihaaA ihbbB
      apply IsType.sigma_form
      · apply ihaaA
      · apply substitution_inv_type
        · rfl
        · apply ihbbB
        · apply boundary_has_type haaA
    case IsEqualTermSigmaElimEq =>
      intro n Γ A B A' B' p p' C C' c c' hSiSi hppSi hCC hccC ihSiSi ihppSi ihCC ihccC
      apply substitution_type
      · apply boundary_has_type hppSi
      · apply ihCC
    case IsEqualTermIdenIntroEq =>
      intro n Γ A A' a a' hAA haaA ihAA ihaA
      have haA := boundary_has_type haaA
      apply IsType.iden_form haA haA
    case IsEqualTermIdenElimEq =>
      intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hIdId hppId ihBB ihbbB ihIdId ihppId
      sorry
    case IsEqualTermTyConvEq =>
      intro n Γ a b A B habA hAB ihabA ihA
      sorry
    any_goals sorry
