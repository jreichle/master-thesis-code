import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Contexts

import aesop

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A))
  :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => Γ ctx)
      (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
      (motive_3 := fun Γ a A _haA => (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type))
      (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
      (motive_5 := fun Γ a a' A _haaA => (Γ ⊢ a ≡ a' ∶ A))
    case IsCtxEmpty =>
      apply IsCtx.empty
    case IsCtxExtend =>
      intro n Γ A hiC hA _ihiC _ihA
      apply IsCtx.extend hiC hA
    case IsTypeUnitForm =>
      intro n Γ hiC _ihiC 
      apply IsEqualType.unit_form_eq hiC
    case IsTypeEmptyForm =>
      intro n Γ hiC _ihiC 
      apply IsEqualType.empty_form_eq hiC
    case IsTypePiForm =>
      intro n Γ A B hA hB ihA ihB
      apply IsEqualType.pi_form_eq ihA ihB
    case IsTypeSigmaForm => 
      intro n Γ A B hA hB ihA ihB
      apply IsEqualType.sigma_form_eq ihA ihB
    case IsTypeIdenForm =>
      intro n Γ a A a' haA haA' ihaA ihaA'
      apply IsEqualType.iden_form_eq
      · apply And.right ihaA
      · apply And.left ihaA
      · apply And.left ihaA'
    case IsTypeUnivForm =>
      intro n Γ hiC _ihiC
      apply IsEqualType.univ_form_eq hiC
    case IsTypeUnivElim =>
      intro n Γ A hAU ihAU
      apply IsEqualType.univ_elim_eq (And.left ihAU)
    case HasTypeVar =>
      intro n Γ A hA ihA
      apply And.intro
      · apply IsEqualTerm.var_eq hA
      · apply weakening_type_eq
        · apply ihA
        · apply hA
    case HasTypeUnitIntro =>
      intro n Γ hiC _ihiC
      apply And.intro
      · apply IsEqualTerm.unit_intro_eq hiC
      · apply IsEqualType.unit_form_eq hiC
    case HasTypePiIntro =>
      intro n Γ A b B hbB ihbB
      apply And.intro
      · apply IsEqualTerm.pi_intro_eq
        · apply And.left ihbB
      · apply IsEqualType.pi_form_eq
        · sorry
        · apply And.right ihbB
    case HasTypeSigmaIntro =>
      intro n Γ a A b B haA hbB ihaA ihbB
      apply And.intro
      · apply IsEqualTerm.sigma_intro_eq
        · apply And.left ihaA
        · apply And.left ihbB
      · apply IsEqualType.sigma_form_eq
        · apply And.right ihaA
        · apply substitution_inv_type_eq
          · rfl
          · rfl
          · apply And.right ihbB
          · apply haA
    case HasTypeIdenIntro =>
      intro n Γ A a haA ihaA
      apply And.intro
      · apply IsEqualTerm.iden_intro_eq
        · apply And.right ihaA
        · apply And.left ihaA
      · apply IsEqualType.iden_form_eq
        · apply And.right ihaA
        · apply And.left ihaA
        · apply And.left ihaA
    case HasTypeUnivUnit =>
      intro n Γ hiC _hiC
      apply And.intro
      · apply IsEqualTerm.univ_unit_eq hiC
      · apply IsEqualType.univ_form_eq hiC
    case HasTypeUnivEmpty =>
      intro n Γ hiC _hiC
      apply And.intro
      · apply IsEqualTerm.univ_empty_eq hiC
      · apply IsEqualType.univ_form_eq hiC
    case HasTypeUnivPi =>
      intro n Γ A B hAU hBU ihAU ihBU
      apply And.intro
      · apply IsEqualTerm.univ_pi_eq
        · apply And.left ihAU
        · apply And.left ihBU
      · apply And.right ihAU
    case HasTypeUnivSigma =>
      intro n Γ A B hAU hBU ihAU ihBU
      apply And.intro
      · apply IsEqualTerm.univ_sigma_eq
        · apply And.left ihAU
        · apply And.left ihBU
      · apply And.right ihAU
    case HasTypeUnivIden =>
      intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA'
      apply And.intro
      · apply IsEqualTerm.univ_iden_eq
        · apply And.left ihAU
        · apply And.left ihaA
        · apply And.left ihaA'
      · apply And.right ihAU
    case HasTypeUnitElim =>
      intro n Γ A a b hA haA hb1 ihA ihaA ihb1
      apply And.intro
      · apply IsEqualTerm.unit_elim_eq
        · apply ihA
        · apply And.left ihaA
        · apply And.left ihb1
      · sorry -- just use subst lemma
    case HasTypeEmptyElim =>
      intro n Γ A b hA hb0 ihA ihb0
      apply And.intro
      · apply IsEqualTerm.empty_elim_eq
        · apply ihA
        · apply And.left ihb0
      · sorry
    case HasTypePiElim =>
      intro n Γ f A B a hfPi haA ihfPi ihaA
      apply And.intro
      · apply IsEqualTerm.pi_elim_eq
        · apply And.left ihfPi
        · apply And.left ihaA
      · sorry
    case HasTypeSigmaElim =>
      intro n Γ A B p C c hpSi hC hcC ihpSi ihC ihcC
      apply And.intro
      · apply IsEqualTerm.sigma_elim_eq
        · apply And.right ihpSi
        · apply And.left ihpSi
        · apply ihC
        · apply And.left ihcC
      · sorry
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p hB hbB hpId ihB ihbB ihpId
      apply And.intro
      · apply IsEqualTerm.iden_elim_eq
        · apply ihB
        · apply And.left ihbB
        · apply And.right ihpId
        · apply And.left ihpId
      · sorry
    case HasTypeTyConv =>
      intro n Γ a A B haA hAB ihaA ihAB
      apply And.intro
      · apply IsEqualTerm.ty_conv_eq
        · apply And.left ihaA
        · apply hAB
      · sorry -- FIXME: use symm, trans
    case IsEqualTermPiComp =>
      intro n Γ A b B a hbB haA ihbB ihaA
      apply IsEqualTerm.pi_comp
      · apply hbB
      · apply haA
    any_goals sorry

theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
  by
    intro hA
    apply (And.left (And.right defeq_refl))
    apply hA

theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    -- apply And.left (And.left (And.right (And.right defeq_refl)))
    -- apply haA
    sorry



mutual
  theorem defeq_refl_type_test : IsType Γ A → IsEqualType Γ A A :=
    by
      intro hA
      apply IsType.recOn
        (motive_1 := fun Γ _hiC => Γ ctx)
        (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
        (motive_3 := fun Γ a A _haA => Γ ⊢ a ∶ A)
        (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
        (motive_5 := fun Γ a a' A _haaA => Γ ⊢ a ≡ a' ∶ A)
        hA
      case iden_form =>
        intro n Γ a A a' haA haA ihaA ihaja
        apply IsEqualType.iden_form_eq
        · sorry
        · sorry
        · sorry
      any_goals sorry

  theorem defeq_refl_term_test : HasType Γ a A → IsEqualTerm Γ a a A :=
    by
      intro haA
      -- apply And.left (And.left (And.right (And.right defeq_refl)))
      -- apply haA
      sorry
end
