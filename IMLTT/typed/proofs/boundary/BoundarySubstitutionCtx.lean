import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

/-# if substiution works, then adding type to context also -/

theorem boundary_subs_type_ctx : 
    Γ ⊢ A⌈σ, b⌉ type → (Γ ⊢ b ∶ B) → Γ ⬝ B ⊢ A⌈⇑ₛσ⌉ type :=
  sorry
