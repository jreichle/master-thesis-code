import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

theorem subst_subst_sigma_c :
    c⌈(ₛidₚ), a, b⌉⌈σ⌉
    = c⌈lift_subst_n 2 σ⌉⌈(ₛidₚ), (a⌈σ⌉), (b⌈σ⌉)⌉ :=
  by
    substitution_step

theorem subst_subst_sigma_C :
    C⌈⇑ₛσ⌉⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ =
    C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌈⇑ₛ⇑ₛσ⌉ :=
  by
    substitution_step
    substitution_step

theorem subst_subst_iden_refl :
    B⌈3ₙ⇑ₛ(σ)⌉⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋⌈⇑ₛ(σ)⌉.refl v(0))⌉
    = B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉⌈⇑ₛ(σ)⌉ :=
  by
    substitution_step

theorem subst_subst_iden_elim :
    B⌈(ₛidₚ), a, b, c⌉⌈σ⌉
    = B⌈lift_subst_n 3 σ⌉⌈(ₛidₚ), (a⌈σ⌉), (b⌈σ⌉), (c⌈σ⌉)⌉ :=
  by
    substitution_step

theorem helper_subst_iden_propagate_subst :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌈⇑ₛ⇑ₛσ⌉
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋⌈⇑ₛ⇑ₛσ⌉] v(0) :=
  by
    substitution_step
    substitution_step

theorem helper_subst_nat_elim {s : Tm l} {A : Tm (n + 2)} :
    A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌈⇑ₛ⇑ₛ(s/ₙhleq)⌉
    = A⌈⇑ₛ(s/ₙhleq)⌉⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ :=
  by
    substitution_step
    substitution_step
