import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

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
    rw [←weaken]
    apply HasType.weak
    · apply hvA
    · apply hB

-- TODO: tactic that takes rule and applies, given that correct conclusion judgment, new goals:
-- - rule assumptions
-- - equality for previous goal to be of judgment form
