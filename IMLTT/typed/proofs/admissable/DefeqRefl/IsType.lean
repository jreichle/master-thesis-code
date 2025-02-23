import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening

import aesop

theorem defeq_refl_unit_form : ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
        ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (B : Tm m), eqM ▸ Γ = Γ_1 ⬝ B → Γ_1 ⊢ B ≡ B type) →
      Γ ⊢ 𝟙 ≡ 𝟙 type :=
  by
    intro n Γ hiC _ihiC
    apply IsEqualType.unit_form_eq hiC

theorem defeq_refl_empty_form : ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
        ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (B : Tm m), eqM ▸ Γ = Γ_1 ⬝ B → Γ_1 ⊢ B ≡ B type) →
      Γ ⊢ 𝟘 ≡ 𝟘 type :=
  by
    intro n Γ hiC _ihiC
    apply IsEqualType.empty_form_eq hiC

theorem defeq_refl_pi_form : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type → Γ ⬝ A ⊢ B type → Γ ⊢ A ≡ A type → Γ ⬝ A ⊢ B ≡ B type → Γ ⊢ ΠA;B ≡ ΠA;B type :=
  by
    intro n Γ A B hA hB ihA ihB
    apply IsEqualType.pi_form_eq ihA ihB

theorem defeq_refl_sigma_form : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type → Γ ⬝ A ⊢ B type → Γ ⊢ A ≡ A type → Γ ⬝ A ⊢ B ≡ B type → Γ ⊢ ΣA;B ≡ ΣA;B type :=
  by
    intro n Γ A B hA hB ihA ihB
    apply IsEqualType.sigma_form_eq ihA ihB

theorem defeq_refl_iden_form : ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
  Γ ⊢ A type →
    (Γ ⊢ a ∶ A) →
      (Γ ⊢ a' ∶ A) →
        Γ ⊢ A ≡ A type →
          ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
              (∀ (eqM : n = 0) (a_5 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_5 → eqM ▸ A = A_1 → ε ⊢ a_5 ≡ a_5 ∶ A_1) ∧
                (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                    eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
                  (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
                    ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1) →
            ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
                (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a' = a → eqM ▸ A = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
                  (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
                    (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
                        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
                      ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
                        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
              Γ ⊢ a ≃[A] a' ≡ a ≃[A] a' type :=
  by
    intro n Γ a A a' hA haA haA' ihA ihaA ihaA'
    cases Γ with
    | empty =>
      simp_all
      aesop
    | extend Γ' B =>
      have ihεAA := And.left ihaA
      have ihεaaA := And.left (And.right ihaA)
      have ihΓBB := And.left (And.right (And.right ihaA))
      have ihΓAA := And.left (And.right (And.right (And.right ihaA)))
      have ihΓaaA := And.right (And.right (And.right (And.right ihaA)))
      have ihΓaaA' := And.right (And.right (And.right (And.right ihaA')))
      simp_all
      apply IsEqualType.iden_form_eq
      · rw [←empty_expand_context (Γ := Γ' ⬝ B)]
        apply ihΓAA
        · rfl
        · rfl
        · rfl
      · rw [←empty_expand_context (Γ := Γ' ⬝ B)]
        apply ihΓaaA
        · rfl
        · rfl
        · rfl
        · rfl
      · rw [←empty_expand_context (Γ := Γ' ⬝ B)]
        apply ihΓaaA'
        · rfl
        · rfl
        · rfl
        · rfl

theorem defeq_refl_univ_form : ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
        ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (B : Tm m), eqM ▸ Γ = Γ_1 ⬝ B → Γ_1 ⊢ B ≡ B type) →
      Γ ⊢ 𝒰 ≡ 𝒰 type :=
  by
    intro n Γ hiC _ihiC
    apply IsEqualType.univ_form_eq hiC

theorem defeq_refl_univ_elim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
  (Γ ⊢ A ∶ 𝒰) →
    ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
        (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
          (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
            (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
              ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
      Γ ⊢ A ≡ A type :=
  by
    intro n Γ A hAU ihAU
    cases Γ with
    | empty =>
      aesop
    | extend Γ' B =>
      have ihεAA := And.left ihAU
      have ihεaaA := And.left (And.right ihAU)
      have ihΓBB := And.left (And.right (And.right ihAU))
      have ihΓAA := And.left (And.right (And.right (And.right ihAU)))
      have ihΓaaA := And.right (And.right (And.right (And.right ihAU)))
      apply IsEqualType.univ_elim_eq
      rw [←empty_expand_context (Γ := Γ' ⬝ B)]
      apply ihΓaaA
      · rfl
      · rfl
      · rfl
      · rfl

-- case IsTypeUnitForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--   Γ ctx →
--     ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
--         ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) →
--       (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟙 = A → ε ⊢ A ≡ A type) ∧
--         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--           ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟙 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type
-- 
-- case IsTypeEmptyForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--   Γ ctx →
--     ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
--         ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) →
--       (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟘 = A → ε ⊢ A ≡ A type) ∧
--         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--           ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟘 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type
-- 
-- case IsTypePiForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--   Γ ⊢ A type →
--     Γ ⬝ A ⊢ B type →
--       ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--         ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ B = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
--                 eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
--                 eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--           (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΠA;B) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type
-- 
-- case IsTypeSigmaForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--   Γ ⊢ A type →
--     Γ ⬝ A ⊢ B type →
--       ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--         ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ B = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
--                 eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
--                 eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--           (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΣA;B) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type
-- 
-- case IsTypeIdenForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
--   Γ ⊢ A type →
--     (Γ ⊢ a ∶ A) →
--       (Γ ⊢ a' ∶ A) →
--         ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--           ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--               (∀ (eqM : n = 0) (a_5 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_5 → eqM ▸ A = A_1 → ε ⊢ a_5 ≡ a_5 ∶ A_1) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                     ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1) →
--             ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                 (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a' = a → eqM ▸ A = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--               (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ a ≃[A] a') = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → (eqM ▸ a ≃[A] a') = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type
-- 
-- case IsTypeUnivForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--   Γ ctx →
--     ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
--         ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) →
--       (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--           ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type
-- 
-- case IsTypeUnivElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
--   (Γ ⊢ A ∶ 𝒰) →
--     ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--         (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--       (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--           ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type
-- 
