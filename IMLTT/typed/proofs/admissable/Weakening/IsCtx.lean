import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.weakening.Helpers
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem weakening_ctx_empty :
    ∀ (l : Nat) {leq : l ≤ 0} {B : Tm l}, get_sub_context ε l leq ⊢ B type → insert_into_ctx leq ε B ctx :=
  by
    intro l hleq B hB
    simp [empty_insert_into_context]
    simp [insert_into_ctx]
    have hiCB := IsCtx.extend (boundary_ctx_type hB) hB
    have heq : l = 0 := by omega
    have B' : Tm 0 := heq ▸ B
    aesop

theorem weakening_extend :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ctx →
      Γ ⊢ A type →
        (∀ (l : Nat) {leq : l ≤ x} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
          (∀ (l : Nat) {leq : l ≤ x} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from x l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ x + 1} {B : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B type → insert_into_ctx leq (Γ ⬝ A) B ctx :=
  by
    intro n Γ A hiC hA ihiC ihA l hLeq B hB
    cases hLeq
    case refl =>
      simp [insert_into_ctx]
      rw [head_get_sub_context] at hB
      apply IsCtx.extend
      · apply boundary_ctx_type hB
        apply rfl
      · apply hB
    case step h =>
      rw [extend_get_sub_context (leq := h)] at hB
      · rw [←extend_insert_into_context]
        apply IsCtx.extend
        · apply ihiC
          apply hB
        · apply ihA
          apply hB
