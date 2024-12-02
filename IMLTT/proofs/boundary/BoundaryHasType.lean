import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.boundary.BoundaryIsCtx

theorem boundary_has_type : IsEqualTerm Γ a a' A → HasType Γ a A :=
  by
    intro haaA
    apply IsEqualTerm.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => HasType Γ a A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A)
      (motive_5 := fun Γ a a' A _haaA => HasType Γ a A)
      haaA
    case unit_comp =>
      intro n Γ A a hA haA _ _
      apply HasType.unit_elim hA haA (HasType.unit_intro (boundary_ctx_term haA))
    case sigma_comp =>
      intro n Γ a A b B C c haA hbB hC hcC _ _ ihC _
      apply HasType.sigma_elim
      · have hiCSi := boundary_ctx_type hC
        match hiCSi with
        | .extend _ hSi => apply hSi
      · apply HasType.sigma_intro haA hbB
      · apply ihC
      · apply hcC
    case iden_comp => 
      intro n Γ A B b a hB hbB _ _ _ ihaA
      apply HasType.iden_elim 
      · apply hB
      · apply hbB
      · apply IsType.iden_form ihaA ihaA
      · apply HasType.iden_intro
        · have hiCAAId := boundary_ctx_type hB
          apply ctx_extr (ctx_decr (ctx_decr hiCAAId))
        · apply ihaA
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop

