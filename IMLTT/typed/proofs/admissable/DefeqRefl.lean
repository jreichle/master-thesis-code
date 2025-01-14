import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import aesop

theorem boundary_is_type_term {n : Nat} {Γ : Ctx n} {s S : Tm n} :
    HasType Γ s S → IsType Γ S := 
  by
    sorry

mutual
  theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
    by
      intro hA
      match hA with
      | .unit_form hiC =>
        apply IsEqualType.unit_form_eq hiC
      | .empty_form hiC =>
        apply IsEqualType.empty_form_eq hiC
      | .pi_form hA hB =>
        apply IsEqualType.pi_form_eq
        · apply defeq_refl_type hA
        · apply defeq_refl_type hB
      | .sigma_form hA hB =>
        apply IsEqualType.sigma_form_eq
        · apply defeq_refl_type hA
        · apply defeq_refl_type hB
      | .iden_form haA haA' =>
        apply IsEqualType.iden_form_eq
        · apply defeq_refl_type (boundary_is_type_term (haA))
        · apply defeq_refl_term haA
        · apply defeq_refl_term haA'
      | .univ_form hiC =>
        have hiC := boundary_ctx_type hA
        apply IsEqualType.univ_form_eq hiC
      | .univ_elim hT =>
        apply IsEqualType.univ_elim_eq
        apply defeq_refl_term hT

  theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
    by
      intro haA
      cases a with
      | unit =>
        cases haA with
        | univ_unit hiC =>
          apply IsEqualTerm.univ_unit_eq hiC
        | ty_conv h1A hAA =>
          apply IsEqualTerm.ty_conv_eq
          · apply IsEqualTerm.univ_unit_eq (boundary_ctx_term h1A)
          · sorry
      | empty =>
        sorry
      | pi A B =>
        sorry
      | sigma A B =>
        sorry
      | iden A a a' =>
        sorry
      | univ =>
        sorry
      | var x =>
        sorry
      | tt =>
        sorry
      | indUnit A b a =>
        sorry
      | indEmpty =>
        sorry
      | lam A b =>
        sorry
      | app f a =>
        sorry
      | pairSigma a b =>
        sorry
      | indSigma A B C c p =>
        sorry
      | refl A a =>
        sorry
      | j A B b a a' p =>
        sorry
      -- intro haA
      -- match haA with
      -- | .var hA hEq =>
      --   apply IsEqualTerm.var_eq
      --   · apply hA
      --   · apply hEq
      -- | .unit_intro hiC =>
      --   apply IsEqualTerm.unit_intro_eq hiC
      -- | .pi_intro hbB =>
      --   apply IsEqualTerm.pi_intro_eq
      --   · apply defeq_refl_term hbB
      --   · apply IsEqualType.pi_form_eq
      --     · apply defeq_refl_type (ctx_extr (boundary_ctx_term hbB))
      --     · sorry -- apply defeq_refl_type (boundary_is_type_term hbB)
      --   · sorry
      -- | .sigma_intro haA hbB =>
      --   sorry
      -- | .iden_intro haA =>
      --   sorry
      -- | .univ_unit hiC =>
      --   sorry
      -- | .univ_empty hiC =>
      --   sorry
      -- | .univ_pi hAU hBU =>
      --   sorry
      -- | .univ_sigma hAU hBU =>
      --   sorry
      -- | .univ_iden hAU haA haA' =>
      --   sorry
      -- | .unit_elim hA haA hb1 hEq =>
      --   sorry
      -- | .empty_elim hA hb0 hEq =>
      --   sorry
      -- | .pi_elim hfPi haA hEq =>
      --   sorry
      -- | .sigma_elim hpSi hC hcC hEq =>
      --   sorry
      -- | .iden_elim hB hbB hpId hB' hEq =>
      --   sorry
      -- | .ty_conv haA hAB =>
      --   sorry
      
end

-- mutual
--   theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
--     by
--       intro hA
--       match A with
--       | .unit =>
--         have hiC := boundary_ctx_type hA
--         apply IsEqualType.unit_form_eq hiC
--       | .empty =>
--         have hiC := boundary_ctx_type hA
--         apply IsEqualType.empty_form_eq hiC
--       | .pi A B =>
--         have hPiInv := pi_is_type_inversion hA
--         apply IsEqualType.pi_form_eq
--         · apply defeq_refl_type (And.left hPiInv)
--         · apply defeq_refl_type (And.right hPiInv)
--       | .sigma A B =>
--         have hSiInv := sigma_is_type_inversion hA
--         apply IsEqualType.sigma_form_eq
--         · apply defeq_refl_type (And.left hSiInv)
--         · apply defeq_refl_type (And.right hSiInv)
--       | .iden A a a' =>
--         have hIdInv := iden_is_type_inversion hA
--         apply IsEqualType.iden_form_eq
--         · apply defeq_refl_type (boundary_is_type_term (And.left hIdInv))
--         · apply defeq_refl_term (And.left hIdInv)
--         · apply defeq_refl_term (And.right hIdInv)
--       | .univ =>
--         have hiC := boundary_ctx_type hA
--         apply IsEqualType.univ_form_eq hiC
--       | .var x =>
--         apply IsEqualType.var_rfl hA
--       | .tt =>
--         sorry
--       | .indUnit A b a =>
--         sorry
--       | .indEmpty A b =>
--         sorry
--       | .lam A b =>
--         sorry
--       | .app f a =>
--         sorry
--       | .pairSigma a b =>
--         sorry
--       | .indSigma A B C c p =>
--         sorry
--       | .refl A a =>
--         sorry
--       | .j A B b a a' p =>
--         sorry
-- 
--   theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
--     by
--       intro haA
--       sorry
-- end

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
      rw [hEq]
      apply And.intro
      · apply IsEqualTerm.var_eq hA rfl
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
        · sorry
        · sorry
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

