import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

theorem helper_weak_subst_nat_elim {leq : l ≤ n} {s : Tm l} {A : Tm (n + 1)} :
    A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌈⇑ₛ⇑ₛ(s↑/ₙhleq)⌉
    = A⌈⇑ₛ(s↑/ₙhleq)⌉⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ :=
  by
    substitution_step
    substitution_step
