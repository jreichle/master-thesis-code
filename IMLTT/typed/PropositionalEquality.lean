import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.WeakSubstitution.WeakSubstitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConv

-- identity of indiscernibles - leibniz principle:
-- ΠA;(ΠA;(v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ≃ (Π(ΠA;B); (x ∶ P(A)) ≃ (y ∶ P(A))))

-- ((ΠP; P⌊↑ₚidₚ⌋)⌊↑ₚ↑ₚidₚ⌋) -> Π P(v(1)); P(v(0))
theorem leibniz_priniple {n : Nat} {Γ : Ctx n} {A p a a' h : Tm n} {B : Tm (n + 3)} {h' P : Tm (n + 1)} :
    -- Γ ⊢ A type
    -- → (Γ ⊢ a ∶ A)
    -- → (Γ ⊢ a' ∶ A)
    (Γ ⊢ p ∶ a ≃[A] a')
    → (Γ ⬝ A ⊢ P type)
    → (Γ ⊢ h ∶ P⌈a⌉₀)
    -- → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ P⌊↑ₚ↑ₚidₚ⌋ type
    → (Γ ⊢ (.j A ((ΠP; P⌊↑ₚidₚ⌋)⌊↑ₚ↑ₚidₚ⌋) (λ(P); v(0)) a a' p) ◃ h ∶ P⌈a'⌉₀)
    :=
  by
    intro hpId hP hhP _
    apply HasType.pi_elim (Γ := Γ) (f := (.j A ((ΠP; P⌊↑ₚidₚ⌋)⌊↑ₚ↑ₚidₚ⌋) (λ(P); v(0)) a a' p)) (a := h)
    sorry
