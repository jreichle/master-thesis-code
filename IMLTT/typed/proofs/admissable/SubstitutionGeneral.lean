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

import IMLTT.typed.proofs.admissable.substitution.Helpers
import IMLTT.typed.proofs.admissable.substitution.IsCtx
import IMLTT.typed.proofs.admissable.substitution.IsType
import IMLTT.typed.proofs.admissable.substitution.HasType
import IMLTT.typed.proofs.admissable.substitution.IsEqualType
import IMLTT.typed.proofs.admissable.substitution.IsEqualTerm

set_option pp.proofs true

theorem substitution :
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {s S : Tm l},
    (Γ ⬝ S ⊗ Δ) ctx → (Γ ⊢ s ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {A : Tm (n + 1)} {s S : Tm l},
    (Γ ⬝ S ⊗ Δ) ⊢ A type → (Γ ⊢ s ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A⌈s/ₙleq⌉ type) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {A a : Tm (n + 1)} {s S : Tm l},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ∶ A) → (Γ ⊢ s ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {A A' : Tm (n + 1)} {s S : Tm l},
    (Γ ⬝ S ⊗ Δ) ⊢ A ≡ A' type → (Γ ⊢ s ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {A a a' : Tm (n + 1)} {s S : Tm l},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⊢ s ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) :=
  by
    suffices h :
      (∀ {n : Nat} {Γ : Ctx n},
          Γ ctx →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
            (A_1 : Tm (m + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (a_1 A_1 : Tm (m + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_1 →
                  eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
            Γ ⊢ A ≡ A' type →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (A_1 A'_1 : Tm (m + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
            (Γ ⊢ a ≡ a' ∶ A) →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (a_1 a'_1 A_1 : Tm (m + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a = a_1 →
                    eqM ▸ a' = a'_1 →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a_1⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉)
      by
        any_goals repeat' (apply And.intro)
        · intro n l hleq Γ Δ s S hiC hsS
          apply (And.left h)
          · apply hiC
          · apply hleq
          · rfl
          · apply hsS
          · rfl
        · intro n l hleq Γ Δ A s S hA hsS
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
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) s S,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → (Γ ⊢ s ∶ S)
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l} A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = A
        → (Γ ⊢ s ∶ S)
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A⌈s/ₙ leq⌉ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) s S a A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = a → eqM ▸ A' = A
        → (Γ ⊢ s ∶ S)
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (a⌈s/ₙ leq⌉) ∶ (A⌈s/ₙ leq⌉))
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) s S A A',
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ C = A → eqM ▸ C' = A'
        → (Γ ⊢ s ∶ S)
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (A⌈s/ₙ leq⌉) ≡ (A'⌈s/ₙ leq⌉) type)
      (motive_5 := fun {n} Γ' c c' C _haaA => 
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) s S a a' A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → (Γ ⊢ s ∶ S)
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (a⌈s/ₙ leq⌉) ≡ (a'⌈s/ₙ leq⌉) ∶ (A⌈s/ₙ leq⌉))
    case IsCtxEmpty =>
      apply substititution_gen_ctx_empty
    case IsCtxExtend =>
      apply substitution_gen_extend
    case IsTypeUnitForm =>
      apply substitution_gen_unit_form
    case IsTypeEmptyForm =>
      apply substitution_gen_empty_form
    case IsTypePiForm =>
      apply substitution_gen_pi_form
    case IsTypeSigmaForm =>
      apply substitution_gen_sigma_form
    case IsTypeNatForm =>
      apply substitution_gen_nat_form
    case IsTypeIdenForm =>
      apply substitution_gen_iden_form
    case IsTypeUnivForm =>
      apply substitution_gen_univ_form
    case IsTypeUnivElim =>
      apply substitution_gen_univ_elim
    case HasTypeVar =>
      apply substitution_gen_var
    case HasTypeWeak =>
      apply substitution_gen_weak
    case HasTypeUnitIntro =>
      apply substitution_gen_unit_intro
    case HasTypePiIntro =>
      apply substitution_gen_pi_intro
    case HasTypeSigmaIntro =>
      apply substitution_gen_sigma_intro
    case HasTypeNatZeroIntro =>
      apply substitution_gen_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply substitution_gen_nat_succ_intro
    case HasTypeIdenIntro =>
      apply substitution_gen_iden_intro
    case HasTypeUnivUnit =>
      apply substitution_gen_univ_unit
    case HasTypeUnivEmpty =>
      apply substitution_gen_univ_empty
    case HasTypeUnivPi =>
      apply substitution_gen_univ_pi
    case HasTypeUnivSigma =>
      apply substitution_gen_univ_sigma
    case HasTypeUnivNat =>
      apply substitution_gen_univ_nat
    case HasTypeUnivIden =>
      apply substitution_gen_univ_iden
    case HasTypeUnitElim =>
      apply substitution_gen_unit_elim
    case HasTypeEmptyElim =>
      apply substitution_gen_empty_elim
    case HasTypePiElim =>
      apply substitution_gen_pi_elim
    case HasTypeSigmaElim =>
      apply substitution_gen_sigma_elim
    case HasTypeNatElim =>
      apply substitution_gen_nat_elim
    case HasTypeIdenElim =>
      apply substitution_gen_iden_elim
    case HasTypeTyConv =>
      apply substitution_gen_ty_conv
    case IsEqualTypeUnitFormEq =>
      apply substitution_gen_unit_form_eq
    case IsEqualTypeEmptyFormEq =>
      apply substitution_gen_empty_form_eq
    case IsEqualTypePiFormEq =>
      apply substitution_gen_pi_form_eq
    case IsEqualTypeSigmaFormEq =>
      apply substitution_gen_sigma_form_eq
    case IsEqualTypeNatFormEq =>
      apply substitution_gen_nat_form_eq
    case IsEqualTypeIdenFormEq =>
      apply substitution_gen_iden_form_eq
    case IsEqualTypeUnivFormEq =>
      apply substitution_gen_univ_form_eq
    case IsEqualTypeUnivElimEq =>
      apply substitution_gen_univ_elim_eq
    case IsEqualTypeTypeSymm =>
      apply substitution_gen_type_symm
    case IsEqualTypeTypeTrans =>
      apply substitution_gen_type_trans
    case IsEqualTermVarEq =>
      apply substitution_gen_var_eq
    case IsEqualTermWeakEq =>
      apply substitution_gen_weak_eq
    case IsEqualTermUnitComp =>
      apply substitution_gen_unit_comp
    case IsEqualTermPiComp =>
      apply substitution_gen_pi_comp
    case IsEqualTermSigmaComp =>
      apply substitution_gen_sigma_comp
    case IsEqualTermNatZeroComp =>
      apply substitution_gen_nat_zero_comp
    case IsEqualTermNatSuccComp =>
      apply substitution_gen_nat_succ_comp
    case IsEqualTermIdenComp =>
      apply substitution_gen_iden_comp
    case IsEqualTermUnitIntroEq =>
      apply substitution_gen_unit_intro_eq
    case IsEqualTermUnitElimEq =>
      apply substitution_gen_unit_elim_eq
    case IsEqualTermEmptyElimEq =>
      apply substitution_gen_empty_elim_eq
    case IsEqualTermPiIntroEq =>
      apply substitution_gen_pi_intro_eq
    case IsEqualTermPiElimEq =>
      apply substitution_gen_pi_elim_eq
    case IsEqualTermSigmaIntroEq =>
      apply substitution_gen_sigma_intro_eq
    case IsEqualTermSigmaElimEq =>
      apply substitution_gen_sigma_elim_eq
    case IsEqualTermNatZeroIntroEq =>
      apply substitution_gen_nat_zero_intro_eq
    case IsEqualTermNatSuccIntroEq =>
      apply substitution_gen_nat_succ_intro_eq
    case IsEqualTermNatElimEq =>
      apply substitution_gen_nat_elim_eq
    case IsEqualTermIdenIntroEq =>
      apply substitution_gen_iden_intro_eq
    case IsEqualTermIdenElimEq =>
      apply substitution_gen_iden_elim_eq
    case IsEqualTermUnivUnitEq =>
      apply substitution_gen_univ_unit_eq
    case IsEqualTermUnivEmptyEq =>
      apply substitution_gen_univ_empty_eq
    case IsEqualTermUnivPiEq =>
      apply substitution_gen_univ_pi_eq
    case IsEqualTermUnivSigmaEq =>
      apply substitution_gen_univ_sigma_eq
    case IsEqualTermUnivNatEq =>
      apply substitution_gen_univ_nat_eq
    case IsEqualTermUnivIdenEq =>
      apply substitution_gen_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply substitution_gen_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply substitution_gen_term_symm
    case IsEqualTermTermTrans =>
      apply substitution_gen_term_trans
