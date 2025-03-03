import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.boundary.HasType
import IMLTT.typed.proofs.boundary.IsEqualType
import IMLTT.typed.proofs.boundary.IsEqualTerm

import Aesop

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
      apply boundary_var
    case HasTypeWeak =>
      apply boundary_weak
    case HasTypeUnitIntro =>
      apply boundary_unit_intro
    case HasTypePiIntro =>
      apply boundary_pi_intro
    case HasTypeSigmaIntro =>
      apply boundary_sigma_intro
    case HasTypeIdenIntro =>
      apply boundary_iden_intro
    case HasTypeUnivUnit =>
      apply boundary_univ_unit
    case HasTypeUnivEmpty =>
      apply boundary_univ_empty
    case HasTypeUnivPi =>
      apply boundary_univ_pi
    case HasTypeUnivSigma =>
      apply boundary_univ_sigma
    case HasTypeUnivIden =>
      apply boundary_univ_iden
    case HasTypeUnitElim =>
      apply boundary_unit_elim
    case HasTypeEmptyElim =>
      apply boundary_empty_elim
    case HasTypePiElim =>
      apply boundary_pi_elim
    case HasTypeSigmaElim =>
      apply boundary_sigma_elim
    case HasTypeIdenElim =>
      apply boundary_iden_elim
    case HasTypeTyConv =>
      apply boundary_ty_conv
    case IsEqualTypeUnitFormEq =>
      apply boundary_unit_form_eq
    case IsEqualTypeEmptyFormEq =>
      apply boundary_empty_form_eq
    case IsEqualTypePiFormEq =>
      apply boundary_pi_form_eq
    case IsEqualTypeSigmaFormEq =>
      apply boundary_sigma_form_eq
    case IsEqualTypeIdenFormEq =>
      apply boundary_iden_form_eq
    case IsEqualTypeUnivFormEq =>
      apply boundary_univ_form_eq
    case IsEqualTypeUnivElimEq =>
      apply boundary_univ_elim_eq
    case IsEqualTypeTypeSymm =>
      apply boundary_type_symm
    case IsEqualTypeTypeTrans =>
      apply boundary_type_trans
    case IsEqualTermVarEq =>
      apply boundary_var_eq
    case IsEqualTermWeakEq =>
      apply boundary_weak_eq
    case IsEqualTermUnitComp =>
      apply boundary_unit_comp
    case IsEqualTermPiComp =>
      apply boundary_pi_comp
    case IsEqualTermSigmaComp =>
      apply boundary_sigma_comp
    case IsEqualTermIdenComp =>
      apply boundary_iden_comp
    case IsEqualTermUnitIntroEq =>
      apply boundary_unit_intro_eq
    case IsEqualTermUnitElimEq =>
      apply boundary_unit_elim_eq
    case IsEqualTermEmptyElimEq =>
      apply boundary_empty_elim_eq
    case IsEqualTermPiIntroEq =>
      apply boundary_pi_intro_eq
    case IsEqualTermPiElimEq =>
      apply boundary_pi_elim_eq
    case IsEqualTermSigmaIntroEq =>
      apply boundary_sigma_intro_eq
    case IsEqualTermSigmaElimEq =>
      apply boundary_sigma_elim_eq
    case IsEqualTermIdenIntroEq =>
      apply boundary_iden_intro_eq
    case IsEqualTermIdenElimEq =>
      apply boundary_iden_elim_eq
    case IsEqualTermUnivUnitEq =>
      apply boundary_univ_unit_eq
    case IsEqualTermUnivEmptyEq =>
      apply boundary_univ_empty_eq
    case IsEqualTermUnivPiEq =>
      apply boundary_univ_pi_eq
    case IsEqualTermUnivSigmaEq =>
      apply boundary_univ_sigma_eq
    case IsEqualTermUnivIdenEq =>
      apply boundary_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply boundary_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply boundary_term_symm
    case IsEqualTermTermTrans =>
      apply boundary_term_trans
    any_goals sorry
