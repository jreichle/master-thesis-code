import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening

import IMLTT.typed.proofs.admissable.defeqrefl.IsCtx
import IMLTT.typed.proofs.admissable.defeqrefl.IsType
import IMLTT.typed.proofs.admissable.defeqrefl.HasType

import aesop

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A))
  :=
  by
    suffices h :
    (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
          ∀ (m : Nat) (z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
            (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
              ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
              (∀ (eqM : n = 0) (a_1 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_1 → eqM ▸ A = A_1 → ε ⊢ a_1 ≡ a_1 ∶ A_1) ∧
                (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                    eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
                  (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
                    ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_1 A_1 : Tm z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_1 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_1 ≡ a_1 ∶ A_1) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A
    by
      any_goals repeat' apply And.intro
      · intro n Γ hiC
        apply hiC
      · intro n Γ A hA
        have ihA := And.left (And.right h) hA
        have ihεAA := And.left ihA
        have ihΓBB := And.left (And.right ihA)
        have ihΓAA := And.right (And.right ihA)
        cases Γ with
        | empty =>
          apply ihεAA
          · rfl
          · rfl
          · rfl
        | extend Γ S =>
          rw [←empty_expand_context (Γ := Γ ⬝ S)]
          apply ihΓAA
          · rfl
          · rfl
          · rfl
      · intro n Γ A a haA
        have ihbB := And.left (And.right (And.right h)) haA
        have ihεAA := And.left ihbB
        have ihεaaA := And.left (And.right ihbB)
        have ihΓBB := And.left (And.right (And.right ihbB))
        have ihΓAA := And.left (And.right (And.right (And.right ihbB)))
        have ihΓaaA := And.right (And.right (And.right (And.right ihbB)))
        cases Γ with
        | empty =>
          apply And.intro
          · apply ihεaaA
            any_goals rfl
          · apply ihεAA
            any_goals rfl
        | extend Γ S =>
          simp_all
          apply And.intro
          · rw [←empty_expand_context (Γ := Γ ⬝ S)]
            apply ihΓaaA
            any_goals rfl
          · rw [←empty_expand_context (Γ := Γ ⬝ S)]
            apply ihΓAA
            any_goals rfl
      · intro n Γ A A' hAA
        apply hAA
      · intro n Γ a a' A haaA
        apply haaA
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        (∀ (eqM : n = 0), eqM ▸ Γ' = ε → (ε ctx)) ∧
        (∀m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          (Γ ⊢ B ≡ B type)))
      (motive_2 := fun {n} Γ' A' _hA => 
        (∀ (eqM : n = 0) A,
          eqM ▸ Γ' = ε → eqM ▸ A' = A →
          (ε ⊢ A ≡ A type)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          Γ ⊢ B ≡ B type) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ A' = A →
          (Γ ⬝ B ⊗ Δ ⊢ A ≡ A type)))
      (motive_3 := fun {n} Γ' a' A' _haA => -- Γ ⊢ a ∶ A → Γ ⊢ A ≡ A type
        (∀ (eqM : n = 0) A,
          eqM ▸ Γ' = ε → eqM ▸ A' = A →
          (ε ⊢ A ≡ A type)) ∧
        (∀ (eqM : n = 0) a A,
          eqM ▸ Γ' = ε → eqM ▸ a' = a → eqM ▸ A' = A →
          (ε ⊢ a ≡ a ∶ A)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          Γ ⊢ B ≡ B type) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ A' = A →
          (Γ ⬝ B ⊗ Δ ⊢ A ≡ A type)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) a A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A' = A →
          (Γ ⬝ B  ⊗ Δ ⊢ a ≡ a ∶ A))
      )
      (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
      (motive_5 := fun Γ a a' A _haaA => Γ ⊢ a ≡ a' ∶ A)
    case IsCtxEmpty =>
      apply defeq_refl_empty
    case IsCtxExtend =>
      apply defeq_refl_extend
    case IsTypeUnitForm =>
      apply defeq_refl_unit_form
    case IsTypeEmptyForm =>
      apply defeq_refl_empty_form
    case IsTypePiForm =>
      apply defeq_refl_pi_form
    case IsTypeSigmaForm =>
      apply defeq_refl_sigma_form
    case IsTypeIdenForm =>
      apply defeq_refl_iden_form
    case IsTypeUnivForm =>
      apply defeq_refl_univ_form
    case IsTypeUnivElim =>
      apply defeq_refl_univ_elim
    -- case HasTypeVar =>
    --   apply defeq_refl_var
    -- case HasTypeWeak =>
    --   apply defeq_refl_weak
    -- case HasTypeUnitIntro =>
    --   apply defeq_refl_unit_intro
    -- case HasTypePiIntro =>
    --   apply defeq_refl_pi_intro
    -- case HasTypeSigmaIntro =>
    --   apply defeq_refl_sigma_intro
    -- case HasTypeIdenIntro =>
    --   apply defeq_refl_iden_intro
    -- case HasTypeUnivUnit =>
    --   apply defeq_refl_univ_unit
    -- case HasTypeUnivEmpty =>
    --   apply defeq_refl_univ_empty
    -- case HasTypeUnivPi =>
    --   apply defeq_refl_univ_pi
    -- case HasTypeUnivSigma =>
    --   apply defeq_refl_univ_sigma
    -- case HasTypeUnivIden =>
    --   apply defeq_refl_univ_iden
    -- case HasTypeUnitElim =>
    --   apply defeq_refl_unit_elim
    -- case HasTypeEmptyElim =>
    --   apply defeq_refl_empty_elim
    -- case HasTypePiElim =>
    --   apply defeq_refl_pi_elim
    -- case HasTypeSigmaElim =>
    --   apply defeq_refl_sigma_elim
    -- case HasTypeIdenElim =>
    --   apply defeq_refl_iden_elim
    -- case HasTypeTyConv =>
    --   apply defeq_refl_ty_conv
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
