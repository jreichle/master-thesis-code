import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import aesop

/- # Γ ⊢ J → Γ ctx -/

theorem ctx_decr : IsCtx (Γ ⬝ A) → IsCtx Γ :=
  by
    intro hiCA
    match hiCA with
    | .extend hiC _ => apply hiC

theorem ctx_extr : IsCtx (Γ ⬝ A) → IsType Γ A :=
  by
    intro hiCA
    match hiCA with
    | .extend _ hA => apply hA

theorem boundary_ctx_term : HasType Γ a A → IsCtx Γ :=
  by
    intro haA
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ _A _hA => IsCtx Γ)
      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
      haA
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop
    · intro n Γ A b B _ hiCA 
      apply ctx_decr hiCA
    · intro n Γ A b b' B _ _ hiCA
      apply ctx_decr hiCA

theorem boundary_ctx_type : IsType Γ A → IsCtx Γ :=
  by
    intro hA
    apply IsType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ _A _hA => IsCtx Γ)
      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
      hA
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop
    · intro n Γ A b B _ hiCA 
      apply ctx_decr hiCA
    · intro n Γ A b b' B _ _ hiCA
      apply ctx_decr hiCA

theorem boundary_ctx_type_eq : IsEqualType Γ A A' → IsCtx Γ :=
  by
    intro hAA
    apply IsEqualType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ _A _hA => IsCtx Γ)
      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
      hAA
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop
    · intro n Γ A b B _ hiCA 
      apply ctx_decr hiCA
    · intro n Γ A b b' B _ _ hiCA
      apply ctx_decr hiCA

theorem boundary_ctx_term_eq : IsEqualTerm Γ a b A → IsCtx Γ :=
  by
    intro haaA
    apply IsEqualTerm.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ _A _hA => IsCtx Γ)
      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
      haaA
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop
    · intro n Γ A b B _ hiCA 
      apply ctx_decr hiCA
    · intro n Γ A b b' B _ _ hiCA
      apply ctx_decr hiCA
