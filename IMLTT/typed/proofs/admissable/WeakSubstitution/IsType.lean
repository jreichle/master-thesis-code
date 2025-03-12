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
import IMLTT.typed.proofs.admissable.WeakeningGeneral
import IMLTT.typed.proofs.admissable.weakSubstitution.WeakSubstitution


theorem test_this_aaaah :
    (Γ ⬝ S) ⊢ A type → (Γ ⬝ S ⊢ b ∶ B)
    → (Γ ⬝ S) ⊢ A⌈(ₛ(↑ₚidₚ)), v(0)⌉ type :=
  by
    intro hA hbB
    sorry

theorem weak_subsitution :
  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
  Γ ⊢ A type →
    Γ ⬝ A ⊢ B type →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {s S : Tm l} (A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ A_1⌈s↑/ₙleq⌉ type) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {s S : Tm l} (A_1 : Tm m),
            eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ A_1⌈s↑/ₙleq⌉ type) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {s S : Tm l} (A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              (eqM ▸ ΠA;B) = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ A_1⌈s↑/ₙleq⌉ type :=
  by
    sorry
