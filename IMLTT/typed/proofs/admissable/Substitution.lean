import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.proofs.Substitution

import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.SubstitutionGeneral

import aesop

/- # Substitution Property -/

theorem substitution_ctx : 
    (Γ ⊢ b ∶ B) → Γ ⬝ B ⬝ A ctx → Γ ⬝ A⌈b⌉₀ ctx :=
  by
    intro hbB hiCBA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    rw [extend_expand_context_n_substitution]
    apply And.left substitution
    · apply hiCBA
    · apply hbB
    omega

theorem substitution_type : (Γ ⊢ b ∶ B) → Γ ⬝ B ⊢ A type → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro hbB hA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right substitution)
    · apply hA
    · apply hbB

theorem substitution_term : 
    (Γ ⊢ b ∶ B) → (Γ ⬝ B ⊢ a ∶ A) → Γ ⊢ a⌈b⌉₀ ∶ A⌈b⌉₀ :=
  by
    intro hbB haA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right (And.right substitution))
    · apply haA
    · apply hbB

theorem substitution_type_eq :
    (Γ ⊢ b ∶ B) → Γ ⬝ B ⊢ A ≡ A' type → Γ ⊢ A⌈b⌉₀ ≡ A'⌈b⌉₀ type :=
  by
    intro hbB hAA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right (And.right (And.right substitution)))
    · apply hAA
    · apply hbB


theorem substitution_term_eq : 
    (Γ ⊢ b ∶ B) → (Γ ⬝ B ⊢ a ≡ a' ∶ A) → Γ ⊢ a⌈b⌉₀ ≡ a'⌈b⌉₀ ∶ A⌈b⌉₀ :=
  by
    intro hbB haaA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.right (And.right (And.right (And.right substitution)))
    · apply haaA
    · apply hbB


-- helper

theorem substitution_inv_type : 
    B' = B⌈a⌉₀ → Γ ⊢ B' type → (Γ ⊢ a ∶ A) → Γ ⬝ A ⊢ B type :=
  by
    intro hBeqB' hBs haA
    match hBs with
    | .unit_form hiC => sorry
    | _ => sorry

theorem substitution_inv_type_eq : 
    B' = B⌈a⌉₀ → C' = C⌈a⌉₀ → Γ ⊢ B' ≡ C' type → (Γ ⊢ a ∶ A) → Γ ⬝ A ⊢ B ≡ C type :=
  by
    sorry

theorem substitution_separate_test :
    A⌈(ₛidₚ), s1, s2, s3⌉ = A⌈s3⌊↑ₚ↑ₚidₚ⌋⌉₀⌈(ₛidₚ), s1, s2⌉ :=
  by
    simp [substitute_zero]
    sorry

theorem substitution_separate_degeneralized : -- TODO: is this provable?
    A⌈(ₛidₚ), s1, s2, s3⌉ = A⌈s3⌊↑ₚ↑ₚidₚ⌋⌉₀⌈s2⌊↑ₚidₚ⌋⌉₀⌈s1⌉₀ :=
  by
    simp [substitute_zero]
    sorry

