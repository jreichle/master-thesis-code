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

import IMLTT.typed.proofs.admissable.substitution.Helpers

theorem substititution_gen_ctx_empty (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) 
  (eqM : 0 = m + 1) (s S : Tm l) :
  eqM ▸ ε = Γ ⬝ S ⊗ Δ → (Γ ⊢ s ∶ S) → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx :=
  by omega

theorem substitution_gen_extend {n : Nat} {Γ : Ctx n} {A : Tm n} (hiC : Γ ctx) (hA : Γ ⊢ A type) :
  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx) →
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
        (A_1 : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type) →
  ∀ (m l : Nat) {leq : l ≤ m} (Γa : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l),
    eqM ▸ Γ ⬝ A = Γa ⬝ S ⊗ Δ → (Γa ⊢ s ∶ S) → (Γa ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx :=
  by
    intro ihiC ihA m l hleq Γ Δ heqM s S heqΓ hsS
    cases heqM
    cases Δ
    case refl.start =>
      simp [substitute_into_gen_ctx]
      simp [expand_ctx]
      simp [expand_ctx] at heqΓ
      rw [←And.left heqΓ]
      exact hiC
    case refl.expand Δ' T =>
      cases n with
      | zero =>
        have h1 := gen_ctx_leq Δ'
        omega
      | succ n' =>
        simp [substitute_into_gen_ctx]
        simp [expand_ctx]
        apply IsCtx.extend
        · apply ihiC
          · have h1 := gen_ctx_leq Δ'
            omega
          · simp_all
            simp [expand_ctx] at heqΓ
            rw [←And.left heqΓ]
          · exact hsS
          · rfl
        · apply ihA
          · simp_all
            simp [expand_ctx] at heqΓ
            rw [←And.left heqΓ]
          · simp_all
            simp [expand_ctx] at heqΓ
            rw [←And.right heqΓ]
          · apply hsS
          · rfl
