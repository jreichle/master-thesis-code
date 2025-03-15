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

import IMLTT.typed.proofs.admissable.weakeningalt.IsCtx
import IMLTT.typed.proofs.admissable.weakeningalt.IsType
import IMLTT.typed.proofs.admissable.weakeningalt.HasType
import IMLTT.typed.proofs.admissable.weakeningalt.IsEqualType
import IMLTT.typed.proofs.admissable.weakeningalt.IsEqualTerm

theorem weakening :
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {S : Tm l},
    (Γ ⊗ Δ) ctx → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ) ctx)) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l},
    (Γ ⊗ Δ) ⊢ A type → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ type) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a : Tm n} {S : Tm l},
    ((Γ ⊗ Δ) ⊢ a ∶ A) → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A A' : Tm n} {S : Tm l},
    (Γ ⊗ Δ) ⊢ A ≡ A' type → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ ≡ A'⌊↑₁n↬l⌋ type) ∧
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a a' : Tm n} {S : Tm l},
    ((Γ ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ≡ a'⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) :=
  by
    suffices h :
        (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
          Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
            Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 A_1 : Tm m),
              Γ_1 ⊢ S type →
                eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ a = a_1 → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
            Γ ⊢ A ≡ A' type →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
                Γ_1 ⊢ S type →
                  eqM ▸ Γ = Γ_1 ⊗ Δ →
                    eqM ▸ A = A_1 → eqM ▸ A' = A'_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
            (Γ ⊢ a ≡ a' ∶ A) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 a'_1 A_1 : Tm m),
                Γ_1 ⊢ S type →
                  eqM ▸ Γ = Γ_1 ⊗ Δ →
                    eqM ▸ a = a_1 →
                      eqM ▸ a' = a'_1 → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋
      by
        any_goals repeat' (apply And.intro)
        · intro n l Γ Δ S hiC hS
          apply (And.left h)
          · apply hiC
          · apply hS
          · rfl
          · rfl
        · intro n l Γ Δ A S hA hS
          apply And.left (And.right h)
          · apply hA
          · apply hS
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A a S haA hS
          apply And.left (And.right (And.right h))
          · apply haA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A A' S hAA hS
          apply And.left (And.right (And.right (And.right h)))
          · apply hAA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A a a' S haaA hS
          apply And.right (And.right (And.right (And.right h)))
          · apply haaA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ)
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ A' = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁m↬l⌋ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S a A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ a' = a → eqM ▸ A' = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a⌊↑₁m↬l⌋) ∶ (A⌊↑₁m↬l⌋))
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S A A',
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ C = A → eqM ▸ C' = A'
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (A⌊↑₁m↬l⌋) ≡ (A'⌊↑₁m↬l⌋) type)
      (motive_5 := fun {n} Γ' c c' C _haaA => 
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S a a' A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a⌊↑₁m↬l⌋) ≡ (a'⌊↑₁m↬l⌋) ∶ (A⌊↑₁m↬l⌋))
    any_goals sorry
