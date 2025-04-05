import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import IMLTT.typed.proofs.admissable.weakening.IsCtx
import IMLTT.typed.proofs.admissable.weakening.IsType
import IMLTT.typed.proofs.admissable.weakening.HasType
import IMLTT.typed.proofs.admissable.weakening.IsEqualType
import IMLTT.typed.proofs.admissable.weakening.IsEqualTerm

theorem weakening :
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {S : Tm l},
    (Γ ⊗ Δ) ctx → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ) ctx)) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l},
    (Γ ⊗ Δ) ⊢ A type → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ type) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a : Tm n} {S : Tm l},
    ((Γ ⊗ Δ) ⊢ a ∶ A) → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A A' : Tm n} {S : Tm l},
    (Γ ⊗ Δ) ⊢ A ≡ A' type → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ ≡ A'⌊↑₁n↬l⌋ type) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a a' : Tm n} {S : Tm l},
    ((Γ ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ≡ a'⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) :=
  by
    suffices h :
        (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
            Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 A_1 : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ a = a_1 → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
            Γ ⊢ A ≡ A' type →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
                Γ_1 ⊢ S type →
                  eqM ▸ Γ = Γ_1 ⊗ Δ →
                    eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
            (Γ ⊢ a ≡ a' ∶ A) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 a'_1 A_1 : Tm m),
                Γ_1 ⊢ S type →
                  eqM ▸ Γ = Γ_1 ⊗ Δ →
                    eqM ▸ a = a_1 →
                      eqM ▸ a' = a'_1 → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋
      by
        any_goals repeat' (apply And.intro)
        · intro n l Γ Δ S hiC hS
          apply (And.left h)
          · apply hiC
          · apply hS
          · rfl
          · rfl
        · intro n l Γ Δ A S hA hS
          apply And.left (And.right h)
          · apply hA
          · apply hS
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A a S haA hS
          apply And.left (And.right (And.right h))
          · apply haA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A A' S hAA hS
          apply And.left (And.right (And.right (And.right h)))
          · apply hAA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A a a' S haaA hS
          apply And.right (And.right (And.right (And.right h)))
          · apply haaA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ)
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ A' = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁m↬l⌋ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S a A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ a' = a → eqM ▸ A' = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a⌊↑₁m↬l⌋) ∶ (A⌊↑₁m↬l⌋))
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S A A',
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ C = A → eqM ▸ C' = A'
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (A⌊↑₁m↬l⌋) ≡ (A'⌊↑₁m↬l⌋) type)
      (motive_5 := fun {n} Γ' c c' C _haaA => 
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S a a' A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a⌊↑₁m↬l⌋) ≡ (a'⌊↑₁m↬l⌋) ∶ (A⌊↑₁m↬l⌋))
    case IsCtxEmpty =>
      apply weakening_gen_empty
    case IsCtxExtend =>
      apply weakening_gen_extend
    case IsTypeUnitForm =>
      apply weakening_unit_form
    case IsTypeEmptyForm =>
      apply weakening_empty_form
    case IsTypePiForm =>
      apply weakening_pi_form
    case IsTypeSigmaForm =>
      apply weakening_sigma_form
    case IsTypeNatForm =>
      apply weakening_nat_form
    case IsTypeIdenForm =>
      apply weakening_iden_form
    case IsTypeUnivForm =>
      apply weakening_univ_form
    case IsTypeUnivElim =>
      apply weakening_univ_elim
    case HasTypeVar =>
      apply weakening_var
    case HasTypeWeak =>
      apply weakening_weak
    case HasTypeUnitIntro =>
      apply weakening_unit_intro
    case HasTypePiIntro =>
      apply weakening_pi_intro
    case HasTypeSigmaIntro =>
      apply weakening_sigma_intro
    case HasTypeNatZeroIntro =>
      apply weakening_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply weakening_nat_succ_intro
    case HasTypeIdenIntro =>
      apply weakening_iden_intro
    case HasTypeUnivUnit =>
      apply weakening_univ_unit
    case HasTypeUnivEmpty =>
      apply weakening_univ_empty
    case HasTypeUnivPi =>
      apply weakening_univ_pi
    case HasTypeUnivSigma =>
      apply weakening_univ_sigma
    case HasTypeUnivNat =>
      apply weakening_univ_nat
    case HasTypeUnivIden =>
      apply weakening_univ_iden
    case HasTypeUnitElim =>
      apply weakening_unit_elim
    case HasTypeEmptyElim =>
      apply weakening_empty_elim
    case HasTypePiElim =>
      apply weakening_pi_elim
    case HasTypeSigmaElim =>
      apply weakening_sigma_elim
    case HasTypeNatElim =>
      apply weakening_nat_elim
    case HasTypeIdenElim =>
      apply weakening_iden_elim
    case HasTypeTyConv =>
      apply weakening_ty_conv
    case IsEqualTypeUnitFormEq =>
      apply weakening_unit_form_eq
    case IsEqualTypeEmptyFormEq =>
      apply weakening_empty_form_eq
    case IsEqualTypePiFormEq =>
      apply weakening_pi_form_eq
    case IsEqualTypeSigmaFormEq =>
      apply weakening_sigma_form_eq
    case IsEqualTypeNatFormEq =>
      apply weakening_nat_form_eq
    case IsEqualTypeIdenFormEq =>
      apply weakening_iden_form_eq
    case IsEqualTypeUnivFormEq =>
      apply weakening_univ_form_eq
    case IsEqualTypeUnivElimEq =>
      apply weakening_univ_elim_eq
    case IsEqualTypeTypeSymm =>
      apply weakening_type_symm
    case IsEqualTypeTypeTrans =>
      apply weakening_type_trans
    case IsEqualTermVarEq =>
      apply weakening_var_eq
    case IsEqualTermWeakEq =>
      apply weakening_weak_eq
    case IsEqualTermUnitComp =>
      apply weakening_unit_comp
    case IsEqualTermPiComp =>
      apply weakening_pi_comp
    case IsEqualTermSigmaComp =>
      apply weakening_sigma_comp
    case IsEqualTermNatZeroComp =>
      apply weakening_nat_zero_comp
    case IsEqualTermNatSuccComp =>
      apply weakening_nat_succ_comp
    case IsEqualTermIdenComp =>
      apply weakening_iden_comp
    case IsEqualTermUnitIntroEq =>
      apply weakening_unit_intro_eq
    case IsEqualTermUnitElimEq =>
      apply weakening_unit_elim_eq
    case IsEqualTermEmptyElimEq =>
      apply weakening_empty_elim_eq
    case IsEqualTermPiIntroEq =>
      apply weakening_pi_intro_eq
    case IsEqualTermPiElimEq =>
      apply weakening_pi_elim_eq
    case IsEqualTermSigmaIntroEq =>
      apply weakening_sigma_intro_eq
    case IsEqualTermSigmaElimEq =>
      apply weakening_sigma_elim_eq
    case IsEqualTermNatZeroIntroEq =>
      apply weakening_nat_zero_intro_eq
    case IsEqualTermNatSuccIntroEq =>
      apply weakening_nat_succ_intro_eq
    case IsEqualTermNatElimEq =>
      apply weakening_nat_elim_eq
    case IsEqualTermIdenIntroEq =>
      apply weakening_iden_intro_eq
    case IsEqualTermIdenElimEq =>
      apply weakening_iden_elim_eq
    case IsEqualTermUnivUnitEq =>
      apply weakening_univ_unit_eq
    case IsEqualTermUnivEmptyEq =>
      apply weakening_univ_empty_eq
    case IsEqualTermUnivPiEq =>
      apply weakening_univ_pi_eq
    case IsEqualTermUnivSigmaEq =>
      apply weakening_univ_sigma_eq
    case IsEqualTermUnivNatEq =>
      apply weakening_univ_nat_eq
    case IsEqualTermUnivIdenEq =>
      apply weakening_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply weakening_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply weakening_term_symm
    case IsEqualTermTermTrans =>
      apply weakening_term_trans
