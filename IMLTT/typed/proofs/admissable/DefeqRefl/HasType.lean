import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

import aesop

theorem defeq_refl_var :
   ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
   Γ ⊢ A type →
   ((∀ (eqM : x = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
       (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
         ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (A_1 : Tm z) (B : Tm m),
           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) →
     (∀ (eqM : x + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
       (∀ (eqM : x + 1 = 0) (a A_1 : Tm 0),
           eqM ▸ Γ ⬝ A = ε → eqM ▸ v(0) = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (B : Tm m),
             eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (A_1 : Tm z) (B : Tm m),
               eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (a A_1 : Tm z) (B : Tm m),
               eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → eqM ▸ v(0) = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1
 :=
  by
    intro n Γ' A hA ihA
    repeat' apply And.intro
    · intro heqM
      omega
    · intro heqM
      omega
    · intro m z Γ Δ heqM B heqΓ
      cases heqM
      cases Δ with
      | start =>
        cases heqΓ
        cases Γ' with
        | empty =>
          apply And.left ihA
          · rfl
          · rfl
          · rfl
        | extend Γ' S =>
          rw [←empty_expand_context (Γ := Γ' ⬝ S)]
          apply And.right (And.right ihA)
          · rfl
          · rfl
          · rfl
      | expand Δ' S =>
        cases heqΓ
        cases Γ with
        | empty =>
          apply And.left (And.right ihA)
          rotate_left
          rotate_left
          · apply Δ'
          · rfl
          · rfl
        | extend Γ S' =>
          apply And.left (And.right ihA)
          rotate_left
          rotate_left
          · apply Δ'
          · rfl
          · rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqT
      cases Δ with
      | start =>
        cases heqΓ
        rw [empty_expand_context]
        apply weakening_type_eq
        · cases Γ' with
          | empty =>
            apply And.left ihA
            · rfl
            · rfl
            · rfl
          | extend Ξ S' =>
            rw [←empty_expand_context (Γ := Ξ ⬝ S')]
            apply And.right (And.right ihA)
            · rfl
            · rfl
            · rfl
        · apply hA
      | expand Δ' S' =>
        cases heqΓ
        apply weakening_type_eq
        · apply And.right (And.right ihA)
          · rfl
          · rfl
          · rfl
        · apply hA
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqt
      cases heqT
      cases Δ with
      | start =>
        cases heqΓ
        rw [empty_expand_context]
        apply IsEqualTerm.var_eq
        apply hA
      | expand Δ' S' =>
        cases heqΓ
        rw [←extend_expand_context]
        apply IsEqualTerm.var_eq
        apply hA

-- case HasTypeWeak
-- 
theorem defeq_refl_weak :
  ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
  (Γ ⊢ v(i) ∶ A) →
  Γ ⊢ B type →
     ((∀ (eqM : x = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
         (∀ (eqM : x = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ v(i) = a → eqM ▸ A = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (A_1 : Tm z) (B : Tm m),
                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (a A_1 : Tm z) (B : Tm m),
                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ v(i) = a → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
       ((∀ (eqM : x = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ B = A → ε ⊢ A ≡ A type) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (A : Tm z) (B_1 : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type) →
         (∀ (eqM : x + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ B = ε → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
           (∀ (eqM : x + 1 = 0) (a A_1 : Tm 0),
               eqM ▸ Γ ⬝ B = ε → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (B_1 : Tm m),
                 eqM ▸ Γ ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ → Γ_1 ⊢ B_1 ≡ B_1 type) ∧
               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
                   eqM ▸ Γ ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
                   eqM ▸ Γ ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ →
                     eqM ▸ v(i)⌊↑ₚidₚ⌋ = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n x Γ' A B hvA hB ihvA ihB
    repeat' apply And.intro
    · intro heqM
      omega
    · intro heqM
      omega
    · intro m z Γ Δ heqM S heqΓ
      have ihεAA := And.left ihvA
      have ihεaaA := And.left (And.right ihvA)
      have ihΓBB := And.left (And.right (And.right ihvA))
      have ihΓAA := And.left (And.right (And.right (And.right ihvA)))
      have ihΓaaA := And.right (And.right (And.right (And.right ihvA)))
      cases heqM
      cases Δ with
      | start =>
        cases heqΓ
        cases Γ' with
        | empty =>
          apply And.left ihB
          · rfl
          · rfl
          · rfl
        | extend Γ' S' =>
          rw [←empty_expand_context (Γ := Γ' ⬝ S')]
          apply And.right (And.right ihB)
          · rfl
          · rfl
          · rfl
      | expand Δ' S' =>
        cases heqΓ
        apply And.left (And.right ihB)
        rotate_left
        · apply n
        · apply Δ'
        · rfl
        · rfl
    · intro m z Γ Δ heqM T B heqΓ heqT
      have ihεAA := And.left ihvA
      have ihεaaA := And.left (And.right ihvA)
      have ihΓBB := And.left (And.right (And.right ihvA))
      have ihΓAA := And.left (And.right (And.right (And.right ihvA)))
      have ihΓaaA := And.right (And.right (And.right (And.right ihvA)))
      cases heqM
      cases heqT
      cases Δ with
      | start =>
        cases heqΓ
        apply weakening_type_eq
        · cases Γ' with
          | empty =>
            apply ihεAA
            · rfl
            · rfl
            · rfl
          | extend Ξ S' =>
            rw [←empty_expand_context (Γ := Ξ ⬝ S')]
            apply ihΓAA
            · rfl
            · rfl
            · rfl
        · apply hB
      | expand Δ' S' =>
        cases heqΓ
        apply weakening_type_eq
        · apply ihΓAA
          · rfl
          · rfl
          · rfl
        · apply hB
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      have ihεAA := And.left ihvA
      have ihεaaA := And.left (And.right ihvA)
      have ihΓBB := And.left (And.right (And.right ihvA))
      have ihΓAA := And.left (And.right (And.right (And.right ihvA)))
      have ihΓaaA := And.right (And.right (And.right (And.right ihvA)))
      cases heqM
      cases heqt
      cases heqT
      cases Δ with
      | start =>
        cases heqΓ
        apply IsEqualTerm.weak_eq
        · cases Γ' with
          | empty =>
            apply ihεaaA
            · rfl
            · rfl
            · rfl
            · rfl
          | extend Γ' S' =>
            rw [←empty_expand_context (Γ := Γ' ⬝ S')]
            apply ihΓaaA
            · rfl
            · rfl
            · rfl
            · rfl
        · apply hB
      | expand Δ' S' =>
        cases heqΓ
        apply IsEqualTerm.weak_eq
        · apply ihΓaaA
          · rfl
          · rfl
          · rfl
          · rfl
        · apply hB

theorem defeq_refl_unit_intro :
  ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
   ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) →
     (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟙 = A → ε ⊢ A ≡ A type) ∧
       (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ ⋆ = a → eqM ▸ 𝟙 = A → ε ⊢ a ≡ a ∶ A) ∧
         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟙 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ ⋆ = a → eqM ▸ 𝟙 = A → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.unit_form_eq
      apply hiC
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_intro_eq
      apply hiC
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      cases Δ
      case start =>
        apply And.right ihiC
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl
      case expand n' Δ' S =>
        apply And.right ihiC
        rotate_left
        · apply n' + 1
        · apply Δ' ⊙ S
        · rfl
        · rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.unit_form_eq
      apply hiC
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_intro_eq
      apply hiC

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
    intro n Γ' A b B hbB h
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.pi_form_eq
      · rw [←empty_expand_context (Γ := ε)]
        apply And.left h
        rotate_left
        · apply 1
        · apply CtxGen.start
        · rfl
        · rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.left (And.right h)
        repeat' rfl
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.pi_intro_eq
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.right (And.right h)
        repeat' rfl
      · apply And.left h
        rotate_left
        · apply 1
        · apply CtxGen.start
        · rfl
        · rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      simp_all
      apply And.left h
      rotate_left
      · apply n + 1
      · apply Δ ⊙ A
      · rfl
      · rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.pi_form_eq
      · rw [←empty_expand_context (Γ := Γ ⬝ S ⊗ Δ)]
        apply And.left h
        rotate_left
        · apply n + 1
        · apply CtxGen.start
        · rfl
        · rfl
      · rw [extend_expand_context]
        apply And.left (And.right h)
        repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.pi_intro_eq
      · rw [extend_expand_context]
        apply And.right (And.right h)
        repeat' rfl
      · rw [←empty_expand_context (Γ := Γ ⬝ S ⊗ Δ)]
        apply And.left h
        rotate_left
        · apply n + 1
        · apply CtxGen.start
        · rfl
        · rfl

theorem defeq_refl_sigma_intro :
   ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
   (Γ ⊢ a ∶ A) →
   (Γ ⊢ b ∶ B⌈a⌉₀) →
     ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
         (∀ (eqM : n = 0) (a_3 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_3 → eqM ▸ A = A_1 → ε ⊢ a_3 ≡ a_3 ∶ A_1) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_3 A_1 : Tm z) (B : Tm m),
                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_3 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_3 ≡ a_3 ∶ A_1) →
       ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ B⌈a⌉₀ = A → ε ⊢ A ≡ A type) ∧
           (∀ (eqM : n = 0) (a_4 A : Tm 0), eqM ▸ Γ = ε → eqM ▸ b = a_4 → eqM ▸ B⌈a⌉₀ = A → ε ⊢ a_4 ≡ a_4 ∶ A) ∧
             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B_1 : Tm m),
                   eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B⌈a⌉₀ = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type) ∧
                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_4 A : Tm z) (B_1 : Tm m),
                   eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ b = a_4 → eqM ▸ B⌈a⌉₀ = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_4 ≡ a_4 ∶ A) →
         (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΣA;B) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
           (∀ (eqM : n = 0) (a_5 A_1 : Tm 0),
               eqM ▸ Γ = ε → eqM ▸ a&b = a_5 → (eqM ▸ ΣA;B) = A_1 → ε ⊢ a_5 ≡ a_5 ∶ A_1) ∧
             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
                   eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B_1 : Tm m),
                   eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ a&b = a_5 → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1 :=
  by
    intro n Γ' a A b B haA hbB ihaA ihbB
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.sigma_form_eq
      · apply And.left ihaA
      · apply substitution_inv_type_eq
        · rfl
        · rfl
        · apply And.left ihbB
        · apply haA
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.sigma_intro_eq
      · apply And.left (And.right ihaA)
      · apply And.left (And.right ihbB)
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      simp_all
      rw [←empty_expand_context (Γ := Γ)]
      apply And.left (And.right (And.right ihaA))
      rotate_left
      · apply n
      · apply Δ
      · rfl
      · rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.sigma_form_eq
      · rw [←empty_expand_context (Γ := Γ ⬝ S ⊗ Δ)]
        apply And.left (And.right (And.right (And.right ihaA)))
        repeat' rfl
      · apply substitution_inv_type_eq
        · rfl
        · rfl
        · apply And.left (And.right (And.right (And.right ihbB)))
          repeat' rfl
        · apply haA
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.sigma_intro_eq
      · apply And.right (And.right (And.right (And.right ihaA)))
        repeat' rfl
      · apply And.right (And.right (And.right (And.right ihbB)))
        repeat' rfl

theorem defeq_refl_iden_intro :
  ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
  (Γ ⊢ a ∶ A) →
   ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
       (∀ (eqM : n = 0) (a_1 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_1 → eqM ▸ A = A_1 → ε ⊢ a_1 ≡ a_1 ∶ A_1) ∧
         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_1 A_1 : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_1 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_1 ≡ a_1 ∶ A_1) →
     (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ a ≃[A] a) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
       (∀ (eqM : n = 0) (a_3 A_1 : Tm 0),
           eqM ▸ Γ = ε → eqM ▸ A.refl a = a_3 → (eqM ▸ a ≃[A] a) = A_1 → ε ⊢ a_3 ≡ a_3 ∶ A_1) ∧
         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → (eqM ▸ a ≃[A] a) = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_3 A_1 : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A.refl a = a_3 → (eqM ▸ a ≃[A] a) = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_3 ≡ a_3 ∶ A_1 :=
  by
    intro n Γ' A a haA ihaA
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.iden_form_eq
      · apply And.left ihaA
      · apply And.left (And.right ihaA)
      · apply And.left (And.right ihaA)
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.iden_intro_eq
      · apply And.left ihaA
      · apply And.left (And.right ihaA)
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      simp_all
      apply And.left (And.right (And.right ihaA))
      rotate_left
      · apply n
      · apply Δ
      · rfl
      · rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      simp_all
      apply IsEqualType.iden_form_eq
      · apply And.left (And.right (And.right (And.right ihaA)))
        repeat' rfl
      · apply And.right (And.right (And.right (And.right ihaA)))
        repeat' rfl
      · apply And.right (And.right (And.right (And.right ihaA)))
        repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp_all
      apply IsEqualTerm.iden_intro_eq
      · apply And.left (And.right (And.right (And.right ihaA)))
        repeat' rfl
      · apply And.right (And.right (And.right (And.right ihaA)))
        repeat' rfl

theorem defeq_refl_univ_unit :
  ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
   ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) →
     (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
       (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟙 = a → eqM ▸ 𝒰 = A → ε ⊢ a ≡ a ∶ A) ∧
         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
             eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟙 = a → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ' hiC ihiC
    repeat' apply And.intro
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

-- case HasTypeUnivEmpty
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--   Γ ctx →
--     ((∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
--         ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) →
--       (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--         (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟘 = a → eqM ▸ 𝒰 = A → ε ⊢ a ≡ a ∶ A) ∧
--           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--               eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟘 = a → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A
-- 
-- case HasTypeUnivPi
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--   (Γ ⊢ A ∶ 𝒰) →
--     (Γ ⬝ A ⊢ B ∶ 𝒰) →
--       ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--           (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--         ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ 𝒰 = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (eqM : n + 1 = 0) (a A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
--                   eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--           (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--             (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΠA;B) = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΠA;B) = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1
-- 
-- case HasTypeUnivSigma
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--   (Γ ⊢ A ∶ 𝒰) →
--     (Γ ⬝ A ⊢ B ∶ 𝒰) →
--       ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--           (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--         ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ 𝒰 = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (eqM : n + 1 = 0) (a A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
--                   eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--           (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--             (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΣA;B) = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΣA;B) = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1
-- 
-- case HasTypeUnivIden
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
--   (Γ ⊢ A ∶ 𝒰) →
--     (Γ ⊢ a ∶ A) →
--       (Γ ⊢ a' ∶ A) →
--         ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--             (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--           ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--               (∀ (eqM : n = 0) (a_5 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_5 → eqM ▸ A = A_1 → ε ⊢ a_5 ≡ a_5 ∶ A_1) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                     ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1) →
--             ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                 (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a' = a → eqM ▸ A = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--               (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type) ∧
--                 (∀ (eqM : n = 0) (a_7 A_1 : Tm 0),
--                     eqM ▸ Γ = ε → (eqM ▸ a ≃[A] a') = a_7 → eqM ▸ 𝒰 = A_1 → ε ⊢ a_7 ≡ a_7 ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝒰 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_7 A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → (eqM ▸ a ≃[A] a') = a_7 → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_7 ≡ a_7 ∶ A_1
-- 
-- case HasTypeUnitElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
--   Γ ⬝ 𝟙 ⊢ A type →
--     (Γ ⊢ a ∶ A⌈⋆⌉₀) →
--       (Γ ⊢ b ∶ 𝟙) →
--         ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ 𝟙 = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
--                 eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
--                 eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--           ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A⌈⋆⌉₀ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--               (∀ (eqM : n = 0) (a_5 A_1 : Tm 0),
--                   eqM ▸ Γ = ε → eqM ▸ a = a_5 → eqM ▸ A⌈⋆⌉₀ = A_1 → ε ⊢ a_5 ≡ a_5 ∶ A_1) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A⌈⋆⌉₀ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                     ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A⌈⋆⌉₀ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1) →
--             ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟙 = A → ε ⊢ A ≡ A type) ∧
--                 (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ b = a → eqM ▸ 𝟙 = A → ε ⊢ a ≡ a ∶ A) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟙 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ b = a → eqM ▸ 𝟙 = A → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A) →
--               (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A⌈b⌉₀ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                 (∀ (eqM : n = 0) (a_7 A_1 : Tm 0),
--                     eqM ▸ Γ = ε → eqM ▸ A.indUnit b a = a_7 → eqM ▸ A⌈b⌉₀ = A_1 → ε ⊢ a_7 ≡ a_7 ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A⌈b⌉₀ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_7 A_1 : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ →
--                           eqM ▸ A.indUnit b a = a_7 → eqM ▸ A⌈b⌉₀ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_7 ≡ a_7 ∶ A_1
-- 
-- case HasTypeEmptyElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
--   Γ ⬝ 𝟘 ⊢ A type →
--     (Γ ⊢ b ∶ 𝟘) →
--       ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ 𝟘 = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--           (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
--               eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--             ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
--               eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--         ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝟘 = A → ε ⊢ A ≡ A type) ∧
--             (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ b = a → eqM ▸ 𝟘 = A → ε ⊢ a ≡ a ∶ A) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ 𝟘 = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ b = a → eqM ▸ 𝟘 = A → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A) →
--           (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A⌈b⌉₀ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (eqM : n = 0) (a A_1 : Tm 0),
--                 eqM ▸ Γ = ε → eqM ▸ A.indEmpty b = a → eqM ▸ A⌈b⌉₀ = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A⌈b⌉₀ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A.indEmpty b = a → eqM ▸ A⌈b⌉₀ = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1
-- 
-- case HasTypePiElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
--   (Γ ⊢ f ∶ ΠA;B) →
--     (Γ ⊢ a ∶ A) →
--       ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΠA;B) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--           (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ f = a → (eqM ▸ ΠA;B) = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ f = a → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--         ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (eqM : n = 0) (a_4 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_4 → eqM ▸ A = A_1 → ε ⊢ a_4 ≡ a_4 ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_4 A_1 : Tm z) (B : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_4 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_4 ≡ a_4 ∶ A_1) →
--           (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ B⌈a⌉₀ = A → ε ⊢ A ≡ A type) ∧
--             (∀ (eqM : n = 0) (a_5 A : Tm 0), eqM ▸ Γ = ε → eqM ▸ f◃a = a_5 → eqM ▸ B⌈a⌉₀ = A → ε ⊢ a_5 ≡ a_5 ∶ A) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B⌈a⌉₀ = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ f◃a = a_5 → eqM ▸ B⌈a⌉₀ = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A
-- 
-- case HasTypeSigmaElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
--   (Γ ⊢ p ∶ ΣA;B) →
--     (Γ ⬝ ΣA;B) ⊢ C type →
--       (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
--         ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ ΣA;B) = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--             (∀ (eqM : n = 0) (a A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ p = a → (eqM ▸ ΣA;B) = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ p = a → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--           ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), (eqM ▸ Γ ⬝ ΣA;B) = ε → eqM ▸ C = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B_1 : Tm m),
--                   (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ B_1 ⊗ Δ → Γ_1 ⊢ B_1 ≡ B_1 type) ∧
--                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
--                   (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ C = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--             ((∀ (eqM : n + 1 + 1 = 0) (A_1 : Tm 0),
--                   eqM ▸ Γ ⬝ A ⬝ B = ε → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                 (∀ (eqM : n + 1 + 1 = 0) (a A_1 : Tm 0),
--                     eqM ▸ Γ ⬝ A ⬝ B = ε → eqM ▸ c = a → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (B_1 : Tm m),
--                       eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ → Γ_1 ⊢ B_1 ≡ B_1 type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
--                         eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ →
--                           eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (a A_1 : Tm z)
--                         (B_1 : Tm m),
--                         eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ →
--                           eqM ▸ c = a → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1) →
--               (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ C⌈p⌉₀ = A → ε ⊢ A ≡ A type) ∧
--                 (∀ (eqM : n = 0) (a A_1 : Tm 0),
--                     eqM ▸ Γ = ε → eqM ▸ A.indSigma B C c p = a → eqM ▸ C⌈p⌉₀ = A_1 → ε ⊢ a ≡ a ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ C⌈p⌉₀ = A → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ →
--                           eqM ▸ A.indSigma B C c p = a → eqM ▸ C⌈p⌉₀ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1
-- 
-- case HasTypeIdenElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a a' p : Tm n},
--   (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
--     (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
--       (Γ ⊢ p ∶ a ≃[A] a') →
--         Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type →
--           ((∀ (eqM : n + 1 + 1 + 1 = 0) (A_1 : Tm 0),
--                 (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = ε → eqM ▸ B = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 + 1 = z) (B : Tm m),
--                   (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
--                   (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ B_1 ⊗ Δ →
--                     eqM ▸ B = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) →
--             ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                 (∀ (eqM : n = 0) (a_6 A_1 : Tm 0),
--                     eqM ▸ Γ = ε → eqM ▸ b = a_6 → eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 → ε ⊢ a_6 ≡ a_6 ∶ A_1) ∧
--                   (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                       eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ →
--                           eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_6 A_1 : Tm z) (B_1 : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ →
--                           eqM ▸ b = a_6 → eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_6 ≡ a_6 ∶ A_1) →
--               ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ a ≃[A] a') = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--                   (∀ (eqM : n = 0) (a_7 A_1 : Tm 0),
--                       eqM ▸ Γ = ε → eqM ▸ p = a_7 → (eqM ▸ a ≃[A] a') = A_1 → ε ⊢ a_7 ≡ a_7 ∶ A_1) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                       (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → (eqM ▸ a ≃[A] a') = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                         ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_7 A_1 : Tm z) (B : Tm m),
--                           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ →
--                             eqM ▸ p = a_7 → (eqM ▸ a ≃[A] a') = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_7 ≡ a_7 ∶ A_1) →
--                 ((∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A → ε ⊢ A ≡ A type) ∧
--                     (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                       ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B_1 : Tm m),
--                         eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type) →
--                   (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A → ε ⊢ A ≡ A type) ∧
--                     (∀ (eqM : n = 0) (a_9 A_1 : Tm 0),
--                         eqM ▸ Γ = ε →
--                           eqM ▸ A.j B b a a' p = a_9 → eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A_1 → ε ⊢ a_9 ≡ a_9 ∶ A_1) ∧
--                       (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                           eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                         (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B_1 : Tm m),
--                             eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type) ∧
--                           ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_9 A_1 : Tm z)
--                             (B_1 : Tm m),
--                             eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ →
--                               eqM ▸ A.j B b a a' p = a_9 →
--                                 eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A_1 → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_9 ≡ a_9 ∶ A_1
-- 
-- case HasTypeTyConv
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
--   (Γ ⊢ a ∶ A) →
--     Γ ⊢ A ≡ B type →
--       ((∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
--           (∀ (eqM : n = 0) (a_3 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_3 → eqM ▸ A = A_1 → ε ⊢ a_3 ≡ a_3 ∶ A_1) ∧
--             (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
--                 ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_3 A_1 : Tm z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_3 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_3 ≡ a_3 ∶ A_1) →
--         Γ ⊢ A ≡ B type →
--           (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ B = A → ε ⊢ A ≡ A type) ∧
--             (∀ (eqM : n = 0) (a_5 A : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_5 → eqM ▸ B = A → ε ⊢ a_5 ≡ a_5 ∶ A) ∧
--               (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
--                   eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
--                 (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ B = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type) ∧
--                   ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A : Tm z) (B_1 : Tm m),
--                     eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ B = A → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A
