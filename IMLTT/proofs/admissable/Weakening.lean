import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

/- # Weakening -/

theorem weakening_ctx : IsCtx (Γ ⬝ A) → IsType Γ B
                        → IsCtx (Γ ⬝ B ⬝ (weaken A (.shift .id))) :=
  by
    sorry

theorem weakening_type : IsType Γ A → IsType Γ B
                         → IsType (Γ ⬝ B) (weaken A (.shift .id)) :=
  by
    sorry

theorem weakening_term : HasType Γ a A → IsType Γ B
                         → HasType (Γ ⬝ B) (weaken a (.shift .id)) 
                           (weaken A (.shift .id)) :=
  by
    sorry

theorem weakening_type_eq : IsEqualType Γ A A' → IsType Γ B
                            → IsEqualType (Γ ⬝ B) (weaken A (.shift .id)) 
                              (weaken A' (.shift .id)) :=
  sorry

-- FIXME: others like this?
-- theorem weakening_type_eq : IsEqualType (concat_ctx Γ Δ) A A' → IsType Γ B
--                             → IsEqualType (Γ ⬝ B, (lift_ctx 0 1 Δ))
--                               (lift (length_ctx Δ) 1 A) (lift (length_ctx Δ) 1 A') :=
--   by
--     sorry

theorem weakening_term_eq : IsEqualTerm Γ a a' A → IsType Γ B
                            → IsEqualTerm (Γ ⬝ B) (weaken a (.shift .id)) 
                              (weaken a' (.shift .id))
                              (weaken A (.shift .id)) :=
  by
    sorry 
