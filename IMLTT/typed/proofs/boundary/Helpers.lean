import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

theorem id_vone_to_vtwo :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌈(ₛ↑ₚidₚ)⋄ (v(Fin.succ 0))⌉
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(1) :=
  by
    substitution_step
    substitution_step
