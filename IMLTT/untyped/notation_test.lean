import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

-- TODO: do terms
-- ind unit
-- ind empty
-- app
-- ind sigma
-- j

theorem weakaa {n : Nat} {Γ : Ctx (n + 1)} {A : Tm n} :
  Γ ctx → Γ ⊢ weaken (.shift .id) A ≡ A⌈↑ₛ(ₛidₚ)⌉ type :=
  sorry

theorem subsss {n : Nat} {Γ : Ctx (n + 1)} {A : Tm n} :
  Γ ctx → Γ ⊢ weaken (.shift .id) A ≡ A⌊↑ₚidₚ⌋ type :=
  sorry

theorem id_id {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} :
  Γ ⊢ A ≃[A] A type → Γ ⊢ A ◃ A type :=
  by
    intro hPi
    sorry

theorem help_match {A : Prop} : A = A' ∧ A → A' :=
  by
    sorry

