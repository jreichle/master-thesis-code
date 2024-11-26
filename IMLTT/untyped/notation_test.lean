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
  Γ ctx → Γ ⊢ weaken A (.shift .id) ≡ A⌈.weak (↑id)⌉ type :=
  sorry

theorem subsss {n : Nat} {Γ : Ctx (n + 1)} {A : Tm n} :
  Γ ctx → Γ ⊢ weaken A (.shift .id) ≡ A⌊↑ id⌋ type :=
  sorry

theorem id_id {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} :
  Γ ⊢ A ℑ A ≃ A type → Γ ⊢ A ◃ A type :=
  by
    intro hPi
    sorry

