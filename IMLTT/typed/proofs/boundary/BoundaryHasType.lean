import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.DefeqRelation

theorem boundary_has_type : IsEqualTerm Γ a a' A → HasType Γ a A :=
  by
    intro haaA
    apply IsEqualTerm.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => HasType Γ a A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A) -- FIXME: extract this?
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
      · apply IsType.iden_form
        · apply (ctx_extr (ctx_decr (ctx_decr (boundary_ctx_type hB))))
        · apply ihaA
        · apply ihaA
      · apply HasType.iden_intro
        · have hiCAAId := boundary_ctx_type hB
          apply ctx_extr (ctx_decr (ctx_decr hiCAAId))
        · apply ihaA
    case iden_form_eq =>
      intro n Γ A A' a₁ a₂ a₃ a₄
      intro hAA _haaA _haaA' ihAA ihaaA ihaaA'
      apply IsType.iden_form
      · apply ihAA
      · apply ihaaA
      · apply HasType.ty_conv ihaaA' (defeq_type_symm hAA)
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop
