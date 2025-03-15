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

-- case IsTypeUnitForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--     Γ ctx →
--       (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
--         ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝟙 = A → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type
-- case IsTypeEmptyForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--     Γ ctx →
--       (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
--         ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝟘 = A → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type
-- case IsTypePiForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--     Γ ⊢ A type →
--       Γ ⬝ A ⊢ B type →
--         (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--             Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) →
--           (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
--               Γ_1 ⊢ S type → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ → eqM ▸ B = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) →
--             ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--               Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (eqM ▸ ΠA;B) = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type
-- case IsTypeSigmaForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--     Γ ⊢ A type →
--       Γ ⬝ A ⊢ B type →
--         (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--             Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) →
--           (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
--               Γ_1 ⊢ S type → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ → eqM ▸ B = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) →
--             ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--               Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (eqM ▸ ΣA;B) = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type
-- case IsTypeNatForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--     Γ ctx →
--       (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
--         ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝒩 = A → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type
-- case IsTypeIdenForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
--     Γ ⊢ A type →
--       (Γ ⊢ a ∶ A) →
--         (Γ ⊢ a' ∶ A) →
--           (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--               Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) →
--             (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A_1 : Tm m),
--                 Γ_1 ⊢ S type →
--                   eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) →
--               (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
--                   Γ_1 ⊢ S type →
--                     eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) →
--                 ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--                   Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (eqM ▸ a ≃[A] a') = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type
-- case IsTypeUnivForm
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--     Γ ctx →
--       (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
--         ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A : Tm m),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ 𝒰 = A → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type
-- case IsTypeUnivElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
--     (Γ ⊢ A ∶ 𝒰) →
--       (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) →
--         ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
--           Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type
