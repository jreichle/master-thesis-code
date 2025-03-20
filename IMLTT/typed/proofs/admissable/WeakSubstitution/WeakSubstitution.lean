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
import IMLTT.typed.proofs.admissable.WeakeningGeneral

import IMLTT.typed.proofs.admissable.weaksubstitution.IsCtx
import IMLTT.typed.proofs.admissable.weaksubstitution.IsType
import IMLTT.typed.proofs.admissable.weaksubstitution.HasType
import IMLTT.typed.proofs.admissable.weaksubstitution.IsEqualType
import IMLTT.typed.proofs.admissable.weaksubstitution.IsEqualTerm

set_option pp.proofs true

theorem helper_weaken_k_from : n + k + 1 = n + 1 + k := by omega

def weaken_k_from (k : Nat) (n : Nat) (l : Nat) : Weak (n + k) n :=
  match n with
  | .zero => shift_weak_n k .id
  | .succ n' =>
    if l < n' + 1 then
      helper_weaken_k_from ▸ .lift (weaken_k_from k n' l)
    else
      shift_weak_n k .id

theorem weak_substitution :
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {S : Tm l} {s : Tm (l + 1)},
    (Γ ⬝ S ⊗ Δ) ctx → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ctx) ∧
  (∀ {n l : Nat} {leq : (l + 1) ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {A : Tm n} {S : Tm l} {s : Tm (l + 1)},
    (Γ ⬝ S ⊗ Δ) ⊢ A type → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ A⌈s↑/ₙleq⌉ type) ∧
  (∀ {n l : Nat} {leq : (l + 1) ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A a : Tm (n)} {S : Tm l} {s : Tm (l + 1)},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ∶ A) → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) ∧
  (∀ {n l : Nat} {leq : (l + 1) ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A A' : Tm (n)} {S : Tm l} {s : Tm (l + 1)},
    (Γ ⬝ S ⊗ Δ) ⊢ A ≡ A' type → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) ∧
  (∀ {n l : Nat} {leq : (l + 1) ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A a a' : Tm (n)} {S : Tm l} {s : Tm (l + 1)},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) :=
  by
    suffices h :
        (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
            (A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
              (S : Tm l) (a_1 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_1 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
            Γ ⊢ A ≡ A' type →
              ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (A_1 A'_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    eqM ▸ A' = A'_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
            (Γ ⊢ a ≡ a' ∶ A) →
              ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_1 a'_1 A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a = a_1 →
                    eqM ▸ a' = a'_1 →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_1⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉
      by
        any_goals repeat' (apply And.intro)
        · intro n l hleq Γ Δ s S hiC hsS
          apply (And.left h)
          · apply hiC
          · apply hleq
          · rfl
          · apply hsS
          · rfl
        · intro n l hleq Γ Δ A S s hA hsS
          apply And.left (And.right h)
          · apply hA
          · rfl
          · rfl
          · apply hsS
          · rfl
        · intro n l hleq Γ Δ A a s S haA hsS
          apply And.left (And.right (And.right h))
          · apply haA
          · rfl
          · rfl
          · rfl
          · apply hsS
          · rfl
        · intro n l hleq Γ Δ A A' s S hAA hsS
          apply And.left (And.right (And.right (And.right h)))
          · apply hAA
          · rfl
          · rfl
          · rfl
          · apply hsS
          · rfl
        · intro n l hleq Γ Δ A a a' s S haaA hsS
          apply And.right (And.right (And.right (And.right h)))
          · apply haaA
          · rfl
          · rfl
          · rfl
          · rfl
          · apply hsS
          · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l {leq : (l + 1) ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s {S : Tm l} A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = A
        → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ A⌈s↑/ₙleq⌉ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l {leq : (l + 1) ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S a A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = a → eqM ▸ A' = A
        → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉)
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l {leq : (l + 1) ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S A A',
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ C = A → eqM ▸ C' = A'
        → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type)
      (motive_5 := fun {n} Γ' c c' C _haaA =>
        ∀ m l {leq : (l + 1) ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S a a' A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉)
    case IsCtxEmpty =>
      apply weak_substitution_empty
    case IsCtxExtend =>
      apply weak_substitution_extend
    case IsTypeUnitForm =>
      apply weak_substitution_unit_form
    case IsTypeEmptyForm =>
      apply weak_substitution_empty_form
    case IsTypePiForm =>
      apply weak_substitution_pi_form
    case IsTypeSigmaForm =>
      apply weak_substitution_sigma_form
    case IsTypeNatForm =>
      apply weak_substitution_nat_form
    case IsTypeIdenForm =>
      apply weak_substitution_iden_form
    case IsTypeUnivForm =>
      apply weak_substitution_univ_form
    case IsTypeUnivElim =>
      apply weak_substitution_univ_elim
    case HasTypeVar =>
      apply weak_substitution_var
    case HasTypeWeak =>
      apply weak_substitution_weak
    case HasTypeUnitIntro =>
      apply weak_substitution_unit_intro
    case HasTypePiIntro =>
      apply weak_substitution_pi_intro
    case HasTypeSigmaIntro =>
      apply weak_substitution_sigma_intro
    case HasTypeNatZeroIntro =>
      apply weak_substitution_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply weak_substitution_nat_succ_intro
    case HasTypeIdenIntro =>
      apply weak_substitution_iden_intro
    case HasTypeUnivUnit =>
      apply weak_substitution_univ_unit
    case HasTypeUnivEmpty =>
      apply weak_substitution_univ_empty
    case HasTypeUnivPi =>
      apply weak_substitution_univ_pi
    case HasTypeUnivSigma =>
      apply weak_substitution_univ_sigma
    case HasTypeUnivNat =>
      apply weak_substitution_univ_nat
    case HasTypeUnivIden =>
      apply weak_substitution_univ_iden
    case HasTypeUnitElim =>
      apply weak_substitution_unit_elim
    case HasTypeEmptyElim =>
      apply weak_substitution_empty_elim
    case HasTypePiElim =>
      apply weak_substitution_pi_elim
    case HasTypeSigmaFirst =>
      apply weak_substitution_sigma_first
    case HasTypeSigmaSecond =>
      apply weak_substitution_sigma_second
    case HasTypeNatElim =>
      apply weak_substitution_nat_elim
    case HasTypeIdenElim =>
      apply weak_substitution_iden_elim
    case HasTypeTyConv =>
      apply weak_substitution_ty_conv
    case IsEqualTypeUnitFormEq =>
      apply weak_substitution_unit_form_eq
    case IsEqualTypeEmptyFormEq =>
      apply weak_substitution_empty_form_eq
    case IsEqualTypePiFormEq =>
      apply weak_substitution_pi_form_eq
    case IsEqualTypeSigmaFormEq =>
      apply weak_substitution_sigma_form_eq
    case IsEqualTypeNatFormEq =>
      apply weak_substitution_nat_form_eq
    case IsEqualTypeIdenFormEq =>
      apply weak_substitution_iden_form_eq
    case IsEqualTypeUnivFormEq =>
      apply weak_substitution_univ_form_eq
    case IsEqualTypeUnivElimEq =>
      apply weak_substitution_univ_elim_eq
    case IsEqualTypeTypeSymm =>
      apply weak_substitution_type_symm
    case IsEqualTypeTypeTrans =>
      apply weak_substitution_type_trans
    case IsEqualTermVarEq =>
      apply weak_substitution_var_eq
    case IsEqualTermWeakEq =>
      apply weak_substitution_weak_eq
    case IsEqualTermUnitComp =>
      apply weak_substitution_unit_comp
    case IsEqualTermPiComp =>
      apply weak_substitution_pi_comp
    case IsEqualTermSigmaFirstComp =>
      apply weak_substitution_sigma_first_comp
    case IsEqualTermSigmaSecondComp =>
      apply weak_substitution_sigma_second_comp
    case IsEqualTermNatZeroComp =>
      apply weak_substitution_nat_zero_comp
    case IsEqualTermNatSuccComp =>
      apply weak_substitution_nat_succ_comp
    case IsEqualTermIdenComp =>
      apply weak_substitution_iden_comp
    case IsEqualTermUnitIntroEq =>
      apply weak_substitution_unit_intro_eq
    case IsEqualTermUnitElimEq =>
      apply weak_substitution_unit_elim_eq
    case IsEqualTermEmptyElimEq =>
      apply weak_substitution_empty_elim_eq
    case IsEqualTermPiIntroEq =>
      apply weak_substitution_pi_intro_eq
    case IsEqualTermPiElimEq =>
      apply weak_substitution_pi_elim_eq
    case IsEqualTermSigmaIntroEq =>
      apply weak_substitution_sigma_intro_eq
    case IsEqualTermSigmaFirstEq =>
      apply weak_substitution_sigma_first_eq
    case IsEqualTermSigmaSecondEq =>
      apply weak_substitution_sigma_second_eq
    case IsEqualTermNatZeroIntroEq =>
      apply weak_substitution_nat_zero_intro_eq
    case IsEqualTermNatSuccIntroEq =>
      apply weak_substitution_nat_succ_intro_eq
    case IsEqualTermNatElimEq =>
      apply weak_substitution_nat_elim_eq
    case IsEqualTermIdenIntroEq =>
      apply weak_substitution_iden_intro_eq
    case IsEqualTermIdenElimEq =>
      apply weak_substitution_iden_elim_eq
    case IsEqualTermUnivUnitEq =>
      apply weak_substitution_univ_unit_eq
    case IsEqualTermUnivEmptyEq =>
      apply weak_substitution_univ_empty_eq
    case IsEqualTermUnivPiEq =>
      apply weak_substitution_univ_pi_eq
    case IsEqualTermUnivSigmaEq =>
      apply weak_substitution_univ_sigma_eq
    case IsEqualTermUnivNatEq =>
      apply weak_substitution_univ_nat_eq
    case IsEqualTermUnivIdenEq =>
      apply weak_substitution_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply weak_substitution_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply weak_substitution_term_symm
    case IsEqualTermTermTrans =>
      apply weak_substitution_term_trans
