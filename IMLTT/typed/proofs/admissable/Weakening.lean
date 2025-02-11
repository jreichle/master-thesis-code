import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.WeakeningGeneral


-- specializations of general weakening theorems

theorem weakening_ctx {n : Nat} {Γ : Ctx n} {A S : Tm n} :
    Γ ⬝ A ctx → Γ ⊢ S type → Γ ⬝ S ⬝ A⌊↑ₚidₚ⌋ ctx :=
  by
    intro hiCA hS
    rw [middle_insert_into_context]
    apply And.left weakening
    · apply hiCA
    · rw [extend_get_sub_context]
      rw [head_get_sub_context]
      · apply hS
      · omega

theorem weakening_type {n : Nat} {Γ : Ctx n} {A B : Tm n} :
    Γ ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro hA hB
    rw [head_insert_into_context]
    rw [←weaken_from_zero]
    apply And.left (And.right weakening)
    · apply hA
    · rw [head_get_sub_context]
      · apply hB
      · rfl
    · omega

theorem weakening_term :
    (Γ ⊢ a ∶ A) → Γ ⊢ B type → Γ ⬝ B ⊢ a⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ :=
  by
    intro haA hB
    rw [head_insert_into_context]
    rw [←weaken_from_zero]
    apply And.left (And.right (And.right weakening))
    · apply haA
    · rw [head_get_sub_context]
      · apply hB
      · rfl
    · omega

theorem weakening_type_eq : 
    Γ ⊢ A ≡ A' type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ ≡ A'⌊↑ₚidₚ⌋ type :=
  by
    intro hAA hB
    rw [head_insert_into_context]
    rw [←weaken_from_zero]
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · rw [head_get_sub_context]
      · apply hB
      · rfl
    · omega

theorem weakening_term_eq : 
    (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ B type → Γ ⬝ B ⊢ a⌊↑ₚidₚ⌋ ≡ a'⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ :=
  by
    intro haaA hB
    rw [head_insert_into_context]
    rw [←weaken_from_zero]
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · rw [head_get_sub_context]
      · apply hB
      · rfl
    · omega

-- second one weaken

theorem weakening_second_type {n : Nat} {Γ : Ctx n} {B S : Tm n} {A : Tm (n + 1)} :
    Γ ⬝ S ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ A⌊⇑ₚ↑ₚidₚ⌋ type :=
  by
    intro hA hB
    rw [middle_insert_into_context]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    · apply And.left (And.right weakening)
      · apply hA
      · rw [extend_get_sub_context]
        rw [head_get_sub_context]
        apply hB
        rfl
    any_goals omega

theorem weakening_second_term {n : Nat} {Γ : Ctx n} {S B : Tm n} {A a : Tm (n + 1)} :
    (Γ ⬝ S ⊢ a ∶ A) → Γ ⊢ B type → Γ ⬝ B ⬝ S⌊↑ₚidₚ⌋ ⊢ a⌊⇑ₚ↑ₚidₚ⌋ ∶ A⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    intro haA hB
    rw [middle_insert_into_context]
    simp_all
    rw [←weaken_from_zero (l := n)]
    rw [lift_weaken_from]
    apply And.left (And.right (And.right weakening))
    · apply haA
    · rw [extend_get_sub_context]
      rw [head_get_sub_context]
      · apply hB
      · rfl
    any_goals omega

set_option pp.proofs true

theorem weakening_second_type_eq {n : Nat} {Γ : Ctx n} {B S : Tm n} {A A' : Tm (n + 1)} :
    Γ ⬝ S ⊢ A ≡ A' type → Γ ⊢ B type
    → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ A⌊⇑ₚ↑ₚidₚ⌋ ≡ A'⌊⇑ₚ↑ₚidₚ⌋ type :=
  by
    intro hAA hB
    rw [middle_insert_into_context]
    simp_all
    rw [←weaken_from_zero (l := n)]
    rw [lift_weaken_from]
    · apply And.left (And.right (And.right (And.right weakening)))
      · apply hAA
      · rw [extend_get_sub_context]
        rw [head_get_sub_context]
        apply hB
        rfl
    any_goals omega

theorem weakening_second_term_eq {n : Nat} {Γ : Ctx n} {B S : Tm n} {a a' A : Tm (n + 1)} :
    (Γ ⬝ S ⊢ a ≡ a' ∶ A) → Γ ⊢ B type 
    → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ a⌊⇑ₚ↑ₚidₚ⌋ ≡ a'⌊⇑ₚ↑ₚidₚ⌋ ∶ A⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    intro haaA hB
    rw [middle_insert_into_context]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · rw [extend_get_sub_context]
      rw [head_get_sub_context]
      · apply hB
      · rfl
    any_goals omega

