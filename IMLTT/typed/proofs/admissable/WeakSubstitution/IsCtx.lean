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
import IMLTT.typed.proofs.admissable.WeakeningGeneral

theorem weak_substitution_empty :
  ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : 0 = m) (s : Tm (l + 1)) (S : Tm l),
    eqM ▸ ε = Γ ⬝ S ⊗ Δ → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx :=
  by
    intro m l hleq Γ Δ heqM s S heqΓ hsS
    have h := gen_ctx_neq Δ
    omega

theorem weak_substitution_extend :
  ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ctx →
      Γ ⊢ A type →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) (S : Tm l),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) {S : Tm l}
              (A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (s : Tm (l + 1))
              (S : Tm l),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx :=
  by
    intro n Γ' A hiC hA ihiC ihA m l hleq Γ Δ heqM s S heqΓ hsS
    cases heqM
    cases Δ
    case refl.start =>
      cases heqΓ
      simp [substitute_shift_into_gen_ctx]
      simp [expand_ctx]
      apply (boundary_ctx_term hsS)
    case refl.expand Δ' T =>
      cases n with
      | zero =>
        have h1 := gen_ctx_leq Δ'
        omega
      | succ n' =>
        cases heqΓ
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        apply IsCtx.extend
        · apply ihiC
          · have h1 := gen_ctx_leq Δ'
            omega
          · simp_all
          · exact hsS
          · rfl
        · apply ihA
          · simp_all
          · simp_all
          · apply hsS
          · rfl


