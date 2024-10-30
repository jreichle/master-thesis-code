import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.admissable.Weakening
import IMLTT.proofs.admissable.Substitution

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
        | assumption
    · apply IsCtx.empty
    · intro n Γ A hiC hA _ _
      apply IsCtx.extend hiC hA
    · intro n Γ A hA hiC
      apply IsCtx.extend hiC hA
    · intro n Γ A b B _ hiCA 
      apply ctx_decr hiCA
    · intro n Γ A hA hiC
      apply IsCtx.extend hiC hA
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
          | assumption
      · apply IsCtx.empty
      · intro n Γ A hiC hA _ _
        apply IsCtx.extend hiC hA
      · intro n Γ A hA hiC
        apply IsCtx.extend hiC hA
      · intro n Γ A b B _ hiCA 
        apply ctx_decr hiCA
      · intro n Γ A hA hiC
        apply IsCtx.extend hiC hA
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
          | assumption
      · apply IsCtx.empty
      · intro n Γ A hiC hA _ _
        apply IsCtx.extend hiC hA
      · intro n Γ A hA hiC
        apply IsCtx.extend hiC hA
      · intro n Γ A b B _ hiCA 
        apply ctx_decr hiCA
      · intro n Γ A hA hiC
        apply IsCtx.extend hiC hA
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
        | assumption
    · apply IsCtx.empty
    · intro n Γ A hiC hA _ _
      apply IsCtx.extend hiC hA
    · intro n Γ A hA hiC
      apply IsCtx.extend hiC hA
    · intro n Γ A b B _ hiCA 
      apply ctx_decr hiCA
    · intro n Γ A hA hiC
      apply IsCtx.extend hiC hA
    · intro n Γ A b b' B _ _ hiCA
      apply ctx_decr hiCA

/- # if hasType, then type is well-formed -/

theorem works : IsType Γ (.pi A B) → IsType (Γ ⬝ A) B :=
  by
    intro hPi
    match hPi with
    | .pi_form hA hB => apply hB
    | .univ_elim hPIU =>
      sorry

-- TODO: if not provable, major rules changes needed
theorem boundary_term_type : HasType Γ a A → IsType Γ A :=
  by
    intro haA
    match haA with
    | .var hA =>
      apply weakening_type hA hA
    | .unit_intro hiC =>
      apply IsType.unit_form hiC
    | .pi_intro hbB =>
      have hB := boundary_term_type hbB
      apply IsType.pi_form 
      · have hiCA := boundary_ctx_type hB
        apply ctx_extr hiCA
      · apply hB
    | .sigma_intro haA hbB =>
      apply IsType.sigma_form
      · apply boundary_term_type haA
      · have hBs := boundary_term_type hbB
        apply substitution_inv_type
        · rfl
        · apply hBs
        · apply haA
    | .iden_intro haA =>
      apply IsType.iden_form haA haA
    -- univ start
    | .univ_unit hiC => 
      apply IsType.univ_form hiC
    | .univ_empty hiC =>
      apply IsType.univ_form hiC
    | .univ_pi hAU hBU =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    | .univ_sigma hAU hBU =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    | .univ_iden hAU haA haA' =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    -- univ end
    | .unit_elim hA haA hb1 =>
      apply substitution_type
      · apply hb1
      · apply hA
    | .empty_elim hA hb0 =>
      apply substitution_type
      · apply hb0
      · apply hA
    | .pi_elim hfPi haA =>
      apply substitution_type
      · apply haA
      · have hPi := boundary_term_type hfPi
        sorry
    | .sigma_elim hpPi hC hcC =>
      apply substitution_type
      · apply hpPi
      · apply hC
    | .iden_elim hB hbB hpI =>
      sorry
    | .ty_conv haA hAB =>
      sorry

theorem boundary_equal_term_type : IsEqualTerm Γ a a' A → IsType Γ A :=
  sorry

/-# if substiution works, then adding type to context also -/

theorem boundary_subs_type_ctx : IsType Γ (substitute A (.extend σ b))  → HasType Γ b B
                                 → IsType (Γ ⬝ B) (substitute A (.lift (σ))) :=
  sorry
