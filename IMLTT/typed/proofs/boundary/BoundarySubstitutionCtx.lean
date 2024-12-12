import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

/-# if substiution works, then adding type to context also -/

theorem boundary_subs_type_ctx : IsType Γ (substitute (.extend σ b) A)  → HasType Γ b B
                                 → IsType (Γ ⬝ B) (substitute (.lift (σ)) A) :=
  sorry
