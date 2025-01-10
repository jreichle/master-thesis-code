import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.Contexts
import IMLTT.typed.proofs.boundary.BoundaryIsType

import aesop

mutual
  theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
    by
      intro hA
      match A with
      | .unit =>
        have hiC := boundary_ctx_type hA
        apply IsEqualType.unit_form_eq hiC
      | .empty =>
        have hiC := boundary_ctx_type hA
        apply IsEqualType.empty_form_eq hiC
      | .pi A B =>
        have hPiInv := pi_is_type_inversion hA
        apply IsEqualType.pi_form_eq
        · apply defeq_refl_type (And.left hPiInv)
        · apply defeq_refl_type (And.right hPiInv)
      | .sigma A B =>
        have hSiInv := sigma_is_type_inversion hA
        apply IsEqualType.sigma_form_eq
        · apply defeq_refl_type (And.left hSiInv)
        · apply defeq_refl_type (And.right hSiInv)
      | .iden A a a' =>
        have hIdInv := iden_is_type_inversion hA
        apply IsEqualType.iden_form_eq
        · apply defeq_refl_type (boundary_is_type_term (And.left hIdInv))
        · apply defeq_refl_term (And.left hIdInv)
        · apply defeq_refl_term (And.right hIdInv)
      | .univ =>
        have hiC := boundary_ctx_type hA
        apply IsEqualType.univ_form_eq hiC
      | .var x =>
        -- use iden form with Γ ⊢ v(0) ∶ 𝒰
        -- apply IsEqualType.iden_form -- wrong kind of equality??
        sorry
      | .tt => sorry
      | .indUnit A b a => sorry
      | .indEmpty A b => sorry
      | .lam A b => sorry
      | .app f a => sorry
      | .pairSigma a b => sorry
      | .indSigma A B C c p => sorry
      | .refl A a => sorry
      | .j A B b a a' p => sorry

  theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
    by
      intro haA
      sorry
end

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A) ∧ (Γ ⊢ A ≡ A type))
  :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => Γ ctx)
      (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
      (motive_3 := fun Γ a A _haA => (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type))
      (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
      (motive_5 := fun Γ a a' A _haaA => (Γ ⊢ a ≡ a' ∶ A) ∧ (Γ ⊢ A ≡ A type))
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
      intro n Γ A S hA hEq ihA
      apply And.intro
      · apply IsEqualTerm.var_eq hA
        sorry
      · sorry
      -- · apply weakening_type_eq
      --   · apply ihA
      --   · apply hA
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
        · sorry -- FIXME: won't work
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
    any_goals sorry

-- theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
--   by
--     intro hA
--     apply (And.left (And.right defeq_refl))
--     apply hA
-- 
-- theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
--   by
--     intro haA
--     -- apply And.left (And.left (And.right (And.right defeq_refl)))
--     -- apply haA
--     sorry

