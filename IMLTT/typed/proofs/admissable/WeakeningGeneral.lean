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
    (∀ {n : Nat} {Γ : Ctx n} (isCtx : Γ ctx)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n} (isType : Γ ⊢ A type)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ⊢ A⌊weaken_from n l⌋ type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n} (hasType : Γ ⊢ a ∶ A)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
        → insert_into_ctx (leq := leq) Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} (isEqualType : Γ ⊢ A ≡ A' type)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n} (isEqualTerm : Γ ⊢ a ≡ a' ∶ A)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋)
    :=
  by
    apply judgment_recursor
      (motive_1 := fun {n} Γ _hiC =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ctx)
      (motive_2 := fun {n} Γ A _hA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ A⌊weaken_from n l⌋ type)
      (motive_3 := fun {n} Γ a A haA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋)
      (motive_4 := fun {n} Γ A A' _hAA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type)
      (motive_5 := fun {n} Γ a a' A _haaA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋)
    case IsCtxEmpty =>
      apply weakening_ctx_empty
    case IsCtxExtend =>
      apply weakening_extend
    case IsTypeUnitForm =>
      apply weakening_unit_form
    case IsTypeEmptyForm =>
      apply weakening_empty_form
    case IsTypePiForm =>
      apply weakening_pi_form
    case IsTypeSigmaForm =>
      apply weakening_sigma_form
    case IsTypeIdenForm =>
      apply weakening_iden_form
    case IsTypeUnivForm =>
      apply weakening_univ_form
    case IsTypeUnivElim =>
      apply weakening_univ_elim
    case HasTypeVar =>
      apply weakening_type_var
    case HasTypeWeak =>
      apply weakening_weak
    case HasTypeUnitIntro =>
      apply weakening_unit_intro
    case HasTypePiIntro =>
      apply weakening_pi_intro
    case HasTypeSigmaIntro =>
      apply weakening_sigma_intro
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
    case HasTypeUnivIden =>
      apply weakening_univ_iden
    case HasTypeUnitElim =>
      apply weakening_unit_elim
    case HasTypeEmptyElim =>
      apply weakening_empty_elim
    case HasTypePiElim =>
      apply weakening_pi_elim
    case HasTypeSigmaFirst =>
      apply weakening_sigma_first
    case HasTypeSigmaSecond =>
      apply weakening_sigma_second
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
    case IsEqualTermSigmaFirstComp =>
      apply weakening_sigma_first_comp
    case IsEqualTermSigmaSecondComp =>
      apply weakening_sigma_second_comp
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
    case IsEqualTermSigmaFirstEq =>
      apply weakening_sigma_first_eq
    case IsEqualTermSigmaSecondEq =>
      apply weakening_sigma_second_eq
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
    case IsEqualTermUnivIdenEq =>
      apply weakening_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply weakening_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply weakening_term_symm
    case IsEqualTermTermTrans =>
      apply weakening_term_trans
