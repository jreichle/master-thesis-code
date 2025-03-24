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

theorem weakening_gen_empty :
    ∀ (m l : Nat) (Γ : Ctx l) (Δ : CtxGen l m) (eqM : 0 = m) (S : Tm l),
      Γ ⊢ S type → eqM ▸ ε = Γ ⊗ Δ → (Γ ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx :=
  by
    intro m l Γ Δ heqM S hS heqΓ
    cases heqM
    cases Δ with
    | start =>
      cases heqΓ
      rw [empty_expand_context_weaken_from]
      simp [expand_ctx]
      apply IsCtx.extend
      · apply IsCtx.empty
      · apply hS

theorem weakening_gen_extend :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
      Γ ctx →
        Γ ⊢ A type →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l),
              Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (A_1 : Tm m),
                Γ_1 ⊢ S type → eqM ▸ Γ = Γ_1 ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x + 1 = m) (S : Tm l),
                Γ_1 ⊢ S type → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx :=
  by
    intro n Γ' A hiC hA ihiC ihA m l Γ Δ heqM S hS heqΓ
    cases heqM
    cases Δ with
    | start =>
      cases heqΓ
      rw [empty_expand_context_weaken_from]
      apply IsCtx.extend
      · apply boundary_ctx_type hS
      · apply hS
    | expand =>
      cases heqΓ
      simp [weaken_from_into_gen_ctx]
      rw [expand_ctx]
      apply IsCtx.extend
      · apply ihiC
        apply hS
        repeat' rfl
      · apply ihA
        apply hS
        repeat' rfl
