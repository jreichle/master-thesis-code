import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

-- widerspruchsbeweis?
-- TODO: might need logical relation

theorem pi_univ_structure : HasType Γ (.pi A B) .univ 
                            → HasType Γ A .univ ∧ HasType (Γ ⬝ A) B .univ :=
  by
    intro hPiU
    match hPiU with
    | .univ_pi hAU hBU => apply And.intro hAU hBU
    | .ty_conv hPiU' hUU => sorry


theorem pi_assumption : IsType Γ (.pi A B) → IsType Γ A ∧ IsType (Γ ⬝ A) B :=
  by
    intro hPi
    match hPi with
    | .pi_form hA hB => 
      apply And.intro hA hB
    | .univ_elim hPiU =>
      match hPiU with
      | .univ_pi hAU hBU =>
        apply And.intro
        · apply IsType.univ_elim hAU
        · apply IsType.univ_elim hBU
      | .ty_conv hPiU' hUU =>
        sorry -- apply HasType.ty_conv hPiU' hUU
