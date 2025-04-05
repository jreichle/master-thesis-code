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

theorem weakening_unit_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
            Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A A' : Tm m),
            Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝟙 = A → eqM ▸ 𝟙 = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.unit_form_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_empty_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A A' : Tm m),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝟘 = A → eqM ▸ 𝟘 = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.empty_form_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_pi_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
            Γ_1 ⊢ S type →
              eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A' : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ →
                  eqM ▸ B = A_1 → eqM ▸ B' = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type) →
            ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ →
                  (eqM ▸ ΠA;B) = A_1 → (eqM ▸ ΠA';B') = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' A A' B B' hAA hBB ihAA ihBB m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.pi_form_eq
    · apply ihAA
      apply hS
      repeat' rfl
    · rw [extend_expand_context_weaken_from]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      apply ihBB
      apply hS
      repeat' rfl
      apply gen_ctx_leq Δ

theorem weakening_sigma_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
            Γ_1 ⊢ S type →
              eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A' : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ →
                  eqM ▸ B = A_1 → eqM ▸ B' = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type) →
            ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ →
                  (eqM ▸ ΣA;B) = A_1 → (eqM ▸ ΣA';B') = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' A A' B B' hAA hBB ihAA ihBB m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.sigma_form_eq
    · apply ihAA
      apply hS
      repeat' rfl
    · rw [extend_expand_context_weaken_from]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      apply ihBB
      apply hS
      repeat' rfl
      apply gen_ctx_leq Δ

theorem weakening_nat_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A A' : Tm m),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝒩 = A → eqM ▸ 𝒩 = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.nat_form_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_iden_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ A' : Tm n},
    Γ ⊢ A ≡ A' type →
      (Γ ⊢ a₁ ≡ a₂ ∶ A) →
        (Γ ⊢ a₃ ≡ a₄ ∶ A') →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ →
                  eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
                Γ_1 ⊢ S type →
                  eqM ▸ Γ = Γ_1 ⊗ Δ →
                    eqM ▸ a₁ = a →
                      eqM ▸ a₂ = a' → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) →
              (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
                  Γ_1 ⊢ S type →
                    eqM ▸ Γ = Γ_1 ⊗ Δ →
                      eqM ▸ a₃ = a →
                        eqM ▸ a₄ = a' → eqM ▸ A' = A → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋) →
                ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
                  Γ_1 ⊢ S type →
                    eqM ▸ Γ = Γ_1 ⊗ Δ →
                      (eqM ▸ a₁ ≃[A] a₃) = A_1 →
                        (eqM ▸ a₂ ≃[A'] a₄) = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA' m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.iden_form_eq
    · apply ihAA
      apply hS
      repeat' rfl
    · apply ihaaA
      apply hS
      repeat' rfl
    · apply ihaaA'
      apply hS
      repeat' rfl

theorem weakening_univ_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A A' : Tm m),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝒰 = A → eqM ▸ 𝒰 = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.univ_form_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
          Γ_1 ⊢ S type →
            eqM ▸ Γ = Γ_1 ⊗ Δ →
              eqM ▸ A = a → eqM ▸ A' = a' → eqM ▸ 𝒰 = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
          Γ_1 ⊢ S type →
            eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ A A' hAAU ihAAU m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.univ_elim_eq
    rw [←weakening_univ]
    apply ihAAU
    apply hS
    repeat' rfl

theorem weakening_type_symm :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    Γ ⊢ A ≡ A' type →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
          Γ_1 ⊢ S type →
            eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type) →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
          Γ_1 ⊢ S type →
            eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A' = A_1 → eqM ▸ A = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' A A' hAA ihAA m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.type_symm
    apply ihAA
    apply hS
    repeat' rfl

theorem weakening_type_trans :
    ∀ {n : Nat} {Γ : Ctx n} {A B C : Tm n},
    Γ ⊢ A ≡ B type →
      Γ ⊢ B ≡ C type →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A' : Tm m),
            Γ_1 ⊢ S type →
              eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ B = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A A' : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ B = A → eqM ▸ C = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type) →
            ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A' : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ C = A' → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type :=
  by
    intro n Γ A B C hAB hBC ihAB ihBC m l Γ Δ heqM S T T' hS heqΓ heqT heqT'
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.type_trans
    · apply ihAB
      apply hS
      repeat' rfl
    · apply ihBC
      apply hS
      repeat' rfl
