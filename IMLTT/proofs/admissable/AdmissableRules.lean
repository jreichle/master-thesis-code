import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules

/- # Universe and Pi/Sigma -/

theorem pi_univ_backwards_fst : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U → IsEqualType Γ A A' :=
  fun hPiPiU : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U ↦
   by
    match hPiPiU with
    | _ => sorry

theorem pi_univ_backwards_snd : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U → IsEqualType (Γ ⬝ A) B B' :=
  fun hPiPiU : IsEqualTerm Γ (Tm.pi A B) (Tm.pi A' B') U ↦
    by
      sorry
