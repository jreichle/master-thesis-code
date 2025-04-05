import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.weakening.WeakeningGeneral

-- specializations of general weakening theorems

theorem weakening_ctx {n : Nat} {Γ : Ctx n} {A S : Tm n} :
    Γ ⬝ A ctx → Γ ⊢ S type → Γ ⬝ S ⬝ A⌊↑ₚidₚ⌋ ctx :=
  by
    intro hiCA hS
    rw [←empty_expand_context (Γ := Γ ⬝ S)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left weakening
    · apply hiCA
    · apply hS
    · omega

theorem weakening_type {n : Nat} {Γ : Ctx n} {A B : Tm n} :
    Γ ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro hA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.left (And.right weakening)
    · apply hA
    · apply hB
    · omega

theorem weakening_term :
    (Γ ⊢ a ∶ A) → Γ ⊢ B type → Γ ⬝ B ⊢ a⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ :=
  by
    intro haA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.left (And.right (And.right weakening))
    · apply haA
    · apply hB
    · omega

theorem weakening_type_eq : 
    Γ ⊢ A ≡ A' type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ ≡ A'⌊↑ₚidₚ⌋ type :=
  by
    intro hAA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · apply hB
    · omega

theorem weakening_term_eq : 
    (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ B type → Γ ⬝ B ⊢ a⌊↑ₚidₚ⌋ ≡ a'⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ :=
  by
    intro haaA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · apply hB
    · omega

-- second one weaken

theorem weakening_second_type {n : Nat} {Γ : Ctx n} {B S : Tm n} {A : Tm (n + 1)} :
    Γ ⬝ S ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ A⌊⇑ₚ↑ₚidₚ⌋ type :=
  by
    intro hA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left (And.right weakening)
    · apply hA
    · apply hB
    any_goals omega

theorem weakening_second_term {n : Nat} {Γ : Ctx n} {S B : Tm n} {A a : Tm (n + 1)} :
    (Γ ⬝ S ⊢ a ∶ A) → Γ ⊢ B type → Γ ⬝ B ⬝ S⌊↑ₚidₚ⌋ ⊢ a⌊⇑ₚ↑ₚidₚ⌋ ∶ A⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    intro haA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left (And.right (And.right weakening))
    · apply haA
    · apply hB
    any_goals omega

theorem weakening_second_type_eq {n : Nat} {Γ : Ctx n} {B S : Tm n} {A A' : Tm (n + 1)} :
    Γ ⬝ S ⊢ A ≡ A' type → Γ ⊢ B type
    → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ A⌊⇑ₚ↑ₚidₚ⌋ ≡ A'⌊⇑ₚ↑ₚidₚ⌋ type :=
  by
    intro hAA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · apply hB
    any_goals omega

theorem weakening_second_term_eq {n : Nat} {Γ : Ctx n} {B S : Tm n} {a a' A : Tm (n + 1)} :
    (Γ ⬝ S ⊢ a ≡ a' ∶ A) → Γ ⊢ B type 
    → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ a⌊⇑ₚ↑ₚidₚ⌋ ≡ a'⌊⇑ₚ↑ₚidₚ⌋ ∶ A⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    intro haaA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · apply hB
    any_goals omega

-- other

theorem useVarwithWeak :
    Γ ⊢ A type → A⌊↑ₚidₚ⌋ = B → Γ ⬝ A ⊢ v(0) ∶ B :=
  by
    intro hA hEq
    cases hEq
    apply HasType.var
    apply hA

theorem useWeakwithWeak :
    (Γ ⊢ v(i) ∶ A) → Γ ⊢ B type → v(i)⌊↑ₚidₚ⌋ = v(j) → A⌊↑ₚidₚ⌋ = A' → Γ ⬝ B ⊢ v(j) ∶ A' :=
  by
    intro hvA hB hEqv heqA
    cases hEqv
    cases heqA
    rw [←weakening_conv_var]
    apply HasType.weak
    · apply hvA
    · apply hB

theorem useWeakTypewithWeak :
    (Γ ⊢ A type) → Γ ⊢ B type → A' = A⌊↑ₚidₚ⌋ → Γ ⬝ B ⊢ A' type :=
  by
    intro haA hB heqA
    cases heqA
    apply weakening_type
    repeat' assumption

theorem useWeakTermwithWeak :
    (Γ ⊢ a ∶ A) → Γ ⊢ B type → a' = a⌊↑ₚidₚ⌋ → A' = A⌊↑ₚidₚ⌋ → Γ ⬝ B ⊢ a' ∶ A' :=
  by
    intro haA hB heqa heqA
    cases heqa
    cases heqA
    apply weakening_term
    repeat' assumption
