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

theorem helper_weakening_sigma_elim_C {leq : l ≤ n}:
    C⌊weaken_from (n + 1) l⌋⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ =
    C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉⌊weaken_from (n + 1 + 1) l⌋ :=
  by
    substitution_norm

theorem helper_weakening_sigma_elim_c :
    c⌈(ₛidₚ)⋄ a⋄ b⌉⌊ρ⌋
    = c⌊2ₙ⇑ₚρ⌋⌈(ₛidₚ)⋄ (a⌊ρ⌋)⋄ (b⌊ρ⌋)⌉ :=
  by
    substitution_norm

theorem helper_weakening_iden_elim_B :
    B⌈(ₛidₚ)⋄ a⋄ b⋄ c⌉⌊ρ⌋
    = B⌊lift_weak_n 3 ρ⌋⌈(ₛidₚ)⋄ (a⌊ρ⌋)⋄ (b⌊ρ⌋)⋄ (c⌊ρ⌋)⌉ :=
  by
    substitution_norm

theorem helper_weakening_iden_elim_B_refl {leq : l ≤ n} :
    B⌊⇑ₚ⇑ₚ↑₁n + 1↬l⌋⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑₁n↬l⌋⌊↑ₚidₚ⌋.refl v(0))⌉
    = B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉⌊↑₁n + 1↬l⌋ :=
  by
    substitution_norm
