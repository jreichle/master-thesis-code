import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

theorem context_conversion_unit_form :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A : Tm m),
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟙 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ A type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' A hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.unit_form
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_empty_form :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A : Tm m),
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟘 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ A type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' A hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.empty_form
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_pi_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
      Γ ⊢ A type →
        Γ ⬝ A ⊢ B type →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type :=
  by
    intro n Γ' A B hA hB ihA ihB m l Γ Δ heqM S S' T hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.pi_form
    · apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_sigma_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
      Γ ⊢ A type →
        Γ ⬝ A ⊢ B type →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type :=
  by
    intro n Γ' A B hA hB ihA ihB m l Γ Δ heqM S S' T hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.sigma_form
    · apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_iden_form :
    ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
      Γ ⊢ A type →
        (Γ ⊢ a ∶ A) →
          (Γ ⊢ a' ∶ A) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
              (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A_1 : Tm m),
                  Γ_1 ⊢ S ≡ S' type →
                    Γ_1 ⊢ S type →
                      Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A_1) →
                (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
                  ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ a ≃[A] a') = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type :=
  by
    intro n Γ' a A a' hA haA haA' ihA ihaA ihaA' m l Γ Δ heqM S S' T hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.iden_form
    · apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA'
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_form :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A : Tm m),
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ A type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' T hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_form
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    (Γ ⊢ A ∶ 𝒰) →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
        Γ_1 ⊢ S ≡ S' type →
          Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
      ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
        Γ_1 ⊢ S ≡ S' type →
          Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type :=
  by
    intro n Γ' A hAU ihAU m l Γ Δ heqM S S' T hSS hS hS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_elim
    apply ihAU
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl
