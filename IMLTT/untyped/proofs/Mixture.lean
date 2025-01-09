import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Conversion
import IMLTT.untyped.proofs.Composition

theorem weak_sub_lift_weak_before_subst :
    G⌊⇑ₚ(ρ ₚ∘ₚρ')⌋⌈a⌉ = G⌊⇑ₚρ'⌋⌊⇑ₚρ⌋⌈a⌉ :=
  by
    simp [weakening_comp]
    simp [comp_weaken]

theorem weak_sub_ :
    t⌈a⌉₁⌊ρ⌋ = t⌊⇑ₚρ⌋⌈a⌊ρ⌋⌉₁ :=
  by
    sorry
