import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.RulesEquality
import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem weakening_unit_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝟙 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T hS heqΓ heqt
    cases heqM
    cases heqΓ
    cases heqt
    apply IsType.unit_form
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_empty_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝟘 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T hS heqΓ heqt
    cases heqM
    cases heqΓ
    cases heqt
    apply IsType.empty_form
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_pi_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type
    → Γ ⬝ A ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ ΠA;B) = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' A B hA hB ihA ihB m l Γ Δ heqM S T hS heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.pi_form
    · apply ihA
      apply hS
      repeat' rfl
    · replace_by_conclusion ihB
      · apply congr
        · rw [←extend_expand_context_weaken_from]
        · substitution_step
      · apply ihB
        apply hS
        repeat' rfl

theorem weakening_sigma_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type
    → Γ ⬝ A ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ ΣA;B) = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' A B hA hB ihA ihB m l Γ Δ heqM S T hS heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.sigma_form
    · apply ihA
      apply hS
      repeat' rfl
    · replace_by_conclusion ihB
      · apply congr
        · rw [←extend_expand_context_weaken_from]
        · substitution_step
      · apply ihB
        apply hS
        repeat' rfl

theorem weakening_nat_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝒩 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T hS heqΓ heqt
    cases heqM
    cases heqΓ
    cases heqt
    apply IsType.nat_form
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_iden_form :
    ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_5
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a' = a
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ a ≃[A] a') = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' a A a' hA haA haA' ihA ihaA ihaA' m l Γ Δ heqM S T hS heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.iden_form
    · apply ihA
      apply hS
      repeat' rfl
    · apply ihaA
      apply hS
      repeat' rfl
    · apply ihaA'
      apply hS
      repeat' rfl

theorem weakening_univ_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝒰 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S T hS heqΓ heqt
    cases heqM
    cases heqΓ
    cases heqt
    apply IsType.univ_form
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type :=
  by
    intro n Γ A hAU ihAU m l Γ Δ heqM S T hS heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_elim
    rw [←weakening_univ]
    apply ihAU
    apply hS
    repeat' rfl
