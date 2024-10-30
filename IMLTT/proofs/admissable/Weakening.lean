import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

-- FIXME: need more general version
-- theorem weakening_type_eq : IsEqualType (concat_ctx Γ Δ) A A' → IsType Γ B
--                             → IsEqualType (Γ ⬝ B, (lift_ctx 0 1 Δ))
--                               (lift (length_ctx Δ) 1 A) (lift (length_ctx Δ) 1 A') :=
--   by
--     sorry

/- # Weakening -/

-- theorem test : HasType Γ a A → IsType Γ B
--                          → HasType (Γ ⬝ B) (weaken a (.shift .id)) 
--                            (weaken A (.shift .id)) :=
--   by
--     intro haA hB
--     apply HasType.recOn
--       (motive_1 := fun Γ _hiC => IsCtx Γ)
--       (motive_2 := fun Γ _A _hA => IsCtx Γ)
--       (motive_3 := fun Γ a A haA => HasType (Γ ⬝ B) (weaken a (.shift .id)) (weaken A (.shift .id)))
--       (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
--       (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
--       haA

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
    intro haA hB
    sorry
    -- match haA with
    -- | .var hA => sorry
    -- | _ => sorry

theorem weakening_type_eq : IsEqualType Γ A A' → IsType Γ B
                            → IsEqualType (Γ ⬝ B) (weaken A (.shift .id)) 
                              (weaken A' (.shift .id)) :=
  sorry


theorem weakening_term_eq : IsEqualTerm Γ a a' A → IsType Γ B
                            → IsEqualTerm (Γ ⬝ B) (weaken a (.shift .id)) 
                              (weaken a' (.shift .id))
                              (weaken A (.shift .id)) :=
  by
    sorry 
