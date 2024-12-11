import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

theorem pi_has_type_inversion : HasType Γ (.pi A B) V → HasType Γ A U ∧ HasType (Γ ⬝ A) B U :=
  by
    intro hPiV
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ x X _haA =>
         ∀ A, ∀ B, ∀ V,
         x = (.pi A B) ∧ X = V → HasType Γ A U ∧ HasType (Γ ⬝ A) B U)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      hPiV
    any_goals aesop

theorem pi_is_type_inversion : IsType Γ (.pi A B) → IsType Γ A ∧ IsType (Γ ⬝ A) B :=
  by
    intro hPi
    match hPi with
    | .pi_form hA hB => 
      apply And.intro hA hB
    | .univ_elim hPiU =>
      have hAUBU := pi_has_type_inversion hPiU
      apply And.intro
      · apply IsType.univ_elim (And.left hAUBU)
      · apply IsType.univ_elim (And.right hAUBU)

theorem sigma_has_type_inversion : HasType Γ (.sigma A B) V → HasType Γ A U ∧ HasType (Γ ⬝ A) B U :=
  by
    intro hSiV
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ x X _haA =>
         ∀ A, ∀ B, ∀ V,
         x = (.sigma A B) ∧ X = V → HasType Γ A U ∧ HasType (Γ ⬝ A) B U)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      hSiV
    any_goals aesop

theorem sigma_is_type_inversion : IsType Γ (.sigma A B) → IsType Γ A ∧ IsType (Γ ⬝ A) B :=
  by
    intro hSi
    match hSi with
    | .sigma_form hA hB =>
      apply And.intro hA hB
    | .univ_elim hSiU =>
      have hAUBU := sigma_has_type_inversion hSiU
      apply And.intro
      · apply IsType.univ_elim (And.left hAUBU)
      · apply IsType.univ_elim (And.right hAUBU)

set_option maxHeartbeats 1000000

theorem iden_has_type_inversion : HasType Γ (.iden A a a') V 
                                  → HasType Γ A U ∧ HasType Γ a A ∧ HasType Γ a' A :=
  by
    intro hIdV
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ x X _haA =>
         ∀ A, ∀ a, ∀ a', ∀ V,
         x = (.iden A a a') ∧ X = V → HasType Γ A U ∧ HasType Γ a A ∧ HasType Γ a' A)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      hIdV
    case ty_conv =>
      intro n Γ a A B _haA _hAB ihaA _ihAB
      intro A a a' V h1
      apply ihaA
      apply And.intro
      · apply (And.left h1)
      · rfl
    any_goals aesop

theorem iden_is_type_inversion : IsType Γ (.iden A a a') 
                                 → HasType Γ a A ∧ HasType Γ a' A :=
  by
    intro hId
    match hId with
    | .iden_form haA haA' => apply And.intro haA haA'
    | .univ_elim hIdU => 
      have h1 := iden_has_type_inversion hIdU
      apply And.right h1
