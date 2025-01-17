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

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A) ∧ (Γ ⊢ A ≡ A type))
  :=
  by
    suffices h :
  (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            (∀ (eqM : n = 0) (a_1 A_1 : Tm 0),
                eqM ▸ Γ = ε → eqM ▸ a = a_1 → eqM ▸ A = A_1 → (ε ⊢ a_1 ≡ a_1 ∶ A_1) ∧ ε ⊢ A_1 ≡ A_1 type) ∧
              ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (a_1 A_1 : Tm (m + 1)) (B : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B →
                  eqM ▸ a = a_1 →
                    eqM ▸ A = A_1 → (Γ_1 ⬝ B ⊢ a_1 ≡ a_1 ∶ A_1) ∧ Γ_1 ⬝ B ⊢ A_1 ≡ A_1 type ∧ Γ_1 ⊢ B ≡ B type) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A) ∧ Γ ⊢ A ≡ A type
      by sorry
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => Γ ctx)
      (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
      (motive_3 := fun {n} Γ' a' A' _haA =>
        (∀ (eqM : n = 0) a A,
          eqM ▸ Γ' = ε → eqM ▸ a' = a → eqM ▸ A' = A →
          (ε ⊢ a ≡ a ∶ A) ∧ (ε ⊢ A ≡ A type)) ∧
        (∀m (Γ : Ctx m) (eqM : n = m + 1) a A B,
          eqM ▸ Γ' = Γ ⬝ B → eqM ▸ a' = a → eqM ▸ A' = A →
          (Γ ⬝ B ⊢ a ≡ a ∶ A) ∧ (Γ ⬝ B ⊢ A ≡ A type) ∧ Γ ⊢ B ≡ B type))
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
      cases Γ with
      | empty =>
        aesop
      | extend Γ' B =>
        aesop
    case IsTypeUnivForm =>
      intro n Γ hiC _ihiC
      apply IsEqualType.univ_form_eq hiC
    case IsTypeUnivElim =>
      intro n Γ A hAU ihAU
      cases Γ with
      | empty =>
        aesop
      | extend Γ' B =>
        aesop
    case HasTypeVar =>
      intro n Γ A hA ihA
      apply Or.inr
      intro n Γ' eqM a' A' B' heqMΓ heqMa heqMA
      cases eqM
      rw [←heqMa] at *
      rw [←heqMA] at *
      apply And.intro
      · rw [←heqMΓ] at *
        constructor
        · apply hA
        · rfl
      · apply And.intro
        · rw [←heqMΓ] at *
          apply weakening_type_eq
          · apply ihA
          · apply hA
        · aesop
    case HasTypeUnitIntro =>
      intro n Γ hiC _ihiC
      apply Or.inr
      intro m Γ' eqM a' A' B' heqMΓ heqMa heqMA
      apply And.intro
      · aesop
      · apply And.intro
        · aesop
        · sorry
    case HasTypePiIntro =>
      intro n Γ A b B hbB ihbB
      apply Or.inr
      intro m Γ' eqM a' A' B' heqMΓ heqMa heqMA
      rw [←heqMΓ]
      rw [←heqMa]
      rw [←heqMA]
      cases eqM
      apply And.intro
      · apply IsEqualTerm.pi_intro_eq
        · aesop
        · constructor
          · have h : (Γ ⬝ A ⊢ b ≡ b ∶ B) ∧ Γ ⬝ A ⊢ B ≡ B type ∧ Γ ⊢ A ≡ A type := 
              by apply Or.elim ihbB
                 · sorry
                 · sorry
            apply And.right (And.right h)
          · sorry
        · aesop
      · apply And.intro
        · apply IsEqualType.pi_form_eq
          · sorry
          · sorry -- apply And.right ihbB
        · sorry
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

theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
  by
    intro hA
    apply (And.left (And.right defeq_refl))
    apply hA

theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    have h := (And.left (And.right (And.right defeq_refl))) haA
    apply And.left h
