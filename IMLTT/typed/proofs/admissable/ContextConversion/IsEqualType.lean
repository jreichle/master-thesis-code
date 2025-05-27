import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.admissable.Weakening

theorem context_conversion_unit_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
        Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
      ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A A' : Tm m),
        Γ_1 ⊢ S ≡ S' type →
          Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟙 = A → eqM ▸ 𝟙 = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A ≡ A' type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.unit_form_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_empty_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A A' : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟘 = A → eqM ▸ 𝟘 = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A ≡ A' type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.empty_form_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_pi_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
      Γ ⊢ A ≡ A' type →
        Γ ⬝ A ⊢ B ≡ B' type →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A' : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A_1 → eqM ▸ B' = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΠA;B) = A_1 → (eqM ▸ ΠA';B') = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type :=
  by
    intro n Γ' A A' B B' hAA hBB ihAA ihBB m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.pi_form_eq
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_sigma_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
      Γ ⊢ A ≡ A' type →
        Γ ⬝ A ⊢ B ≡ B' type →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A' : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A_1 → eqM ▸ B' = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΣA;B) = A_1 → (eqM ▸ ΣA';B') = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type :=
  by
    intro n Γ' A A' B B' hAA hBB ihAA ihBB m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.sigma_form_eq
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_nat_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
        Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
      ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A A' : Tm m),
        Γ_1 ⊢ S ≡ S' type →
          Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝒩 = A → eqM ▸ 𝒩 = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A ≡ A' type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.nat_form_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl


theorem context_conversion_iden_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ A' : Tm n},
      Γ ⊢ A ≡ A' type →
        (Γ ⊢ a₁ ≡ a₂ ∶ A) →
          (Γ ⊢ a₃ ≡ a₄ ∶ A') →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type) →
              (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
                  Γ_1 ⊢ S ≡ S' type →
                    Γ_1 ⊢ S type →
                      Γ_1 ⊢ S' type →
                        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ a₁ = a → eqM ▸ a₂ = a' → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1) →
                (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type →
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a₃ = a → eqM ▸ a₄ = a' → eqM ▸ A' = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A) →
                  ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type →
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                            (eqM ▸ a₁ ≃[A] a₃) = A_1 → (eqM ▸ a₂ ≃[A'] a₄) = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type :=
  by
    intro n Γ' a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA' m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.iden_form_eq
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA'
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A A' : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝒰 = A → eqM ▸ 𝒰 = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A ≡ A' type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.univ_form_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
      (Γ ⊢ A ≡ A' ∶ 𝒰) →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type →
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = a → eqM ▸ A' = a' → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type :=
  by
    intro n Γ' A A' hAAU ihAAU m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.univ_elim_eq
    apply ihAAU
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_type_symm :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
      Γ ⊢ A ≡ A' type →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A' = A_1 → eqM ▸ A = A'_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type :=
  by
    intro n Γ' A A' hAA ihAA m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.type_symm
    apply ihAA
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_type_trans :
    ∀ {n : Nat} {Γ : Ctx n} {A B C : Tm n},
    Γ ⊢ A ≡ B type →
    Γ ⊢ B ≡ C type →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A' : Tm m),
          Γ_1 ⊢ S ≡ S' type →
            Γ_1 ⊢ S type →
              Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ B = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type) →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A A' : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A → eqM ▸ C = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A ≡ A' type) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A' : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ C = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type :=
  by
    intro n Γ' A B C hAB hBC ihAB ihBC m l Γ Δ heqM S S' T T' hSS hS hS' heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.type_trans
    · apply ihAB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihBC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
