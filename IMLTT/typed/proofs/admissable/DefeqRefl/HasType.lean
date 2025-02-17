import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening

import aesop

theorem defeq_refl_pi_intro :
  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
  (Γ ⬝ A ⊢ b ∶ B) →
    ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ B = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
        (∀ (eqM : n + 1 = 0) (a A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ b = a → eqM ▸ B = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
          (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
            (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
                eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
              ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
                eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ b = a → eqM ▸ B = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1) →
      (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΠA;B) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
        (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ λA; b) = a → (eqM ▸ ΠA;B) = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
          (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
            (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
              ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ λA; b) = a → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ' A b B hbB ihbB
    have ihεAA := And.left ihbB
    have ihεaaA := And.left (And.right ihbB)
    have ihΓBB := And.left (And.right (And.right ihbB))
    have ihΓAA := And.left (And.right (And.right (And.right ihbB)))
    have ihΓaaA := And.right (And.right (And.right (And.right ihbB)))
    repeat' apply And.intro
    · intro heq0 T heqΓ heqT
      cases heq0
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.pi_form_eq
      · apply ihΓBB
        rotate_left
        · apply (0 + 1)
        · apply CtxGen.start (n := (0 + 1))
        · rfl
        · rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply ihΓAA
        · rfl
        · rfl
        · rfl
    · intro heq0 t T heqΓ heqt heqT
      cases heq0
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.pi_intro_eq
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply ihΓaaA
        · rfl
        · rfl
        · rfl
        · rfl
      · apply IsEqualType.pi_form_eq
        · apply ihΓBB
          rotate_left
          · apply (0 + 1)
          · apply CtxGen.start (n := (0 + 1))
          · rfl
          · rfl
        · rw [←empty_expand_context (Γ := ε ⬝ A)]
          apply ihΓAA
          · rfl
          · rfl
          · rfl
    · intro m z Γ Δ heqz T heqΓ
      cases heqz
      cases heqΓ
      simp_all
      apply ihΓBB
      rotate_left
      · apply (n + 1)
      · apply Δ ⊙ A
      · rfl
      · rfl
    · intro m z Γ Δ heqz T S heqΓ heqT
      cases heqz
      cases heqΓ
      cases heqT
      apply IsEqualType.pi_form_eq
      · apply ihΓBB
        rotate_left
        · apply (n + 1)
        · apply CtxGen.start (n := (n + 1))
        · rfl
        · rfl
      · rw [extend_expand_context]
        apply ihΓAA
        · rfl
        · rfl
        · rfl
    · intro m z Γ Δ heqz t T S heqΓ heqt heqT
      cases heqz
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.pi_intro_eq
      · rw [extend_expand_context]
        apply ihΓaaA
        · rfl
        · rfl
        · rfl
        · rfl
      · apply IsEqualType.pi_form_eq
        · apply ihΓBB
          rotate_left
          · apply (n + 1)
          · apply CtxGen.start (n := (n + 1))
          · rfl
          · rfl
        · rw [extend_expand_context]
          apply ihΓAA
          · rfl
          · rfl
          · rfl
