import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules

/- # Substitution Property -/

theorem substitution_ctx : HasType Γ a A → IsCtx (Γ ⬝ A ⬝ B)
                           → IsCtx (Γ ⬝ (substitute B a 0)) :=
  sorry

theorem substitution_type : HasType Γ a A → IsType (Γ ⬝ A) B 
                            → IsType Γ (substitute B a 0) :=
  sorry

theorem substitution_term : HasType Γ a A → HasType (Γ ⬝ A) b B
                            → HasType Γ (substitute b A 0) (substitute B A 0) :=
  sorry

theorem substitution_type_eq : HasType Γ a A → IsEqualType (Γ ⬝ A) B B'
                               → IsEqualType Γ (substitute B a 0) (substitute B' a 0) :=
  sorry

theorem substitution_term_eq : HasType Γ a A → IsEqualTerm (Γ ⬝ A) b b' B
                               → IsEqualTerm Γ (substitute b a 0) (substitute b' a 0) (substitute B a 0) :=
  sorry

/- # Substitution inverse -/

theorem substitute_type_eq_inverse : IsEqualType Γ A A' 
                                     = IsEqualType Γ (substitute (substitute A (Tm.var i) j) j i)
                                       (substitute (substitute A' i j) j i) :=
  sorry

-- TODO: not correct -> substitution decrements variables
theorem substitution_type_eq_id : IsEqualType Γ (lift 0 1 A) (lift 0 1 A')
                                  = IsEqualType Γ
                                    (substitute A (Tm.var i) i) (substitute A' (Tm.var i) i) :=
  sorry

theorem substitution_id_lift : substitute A (Tm.var i) i = lift i 1 A := -- FIXME: -1
  by
    sorry

-- TODO: theorem for relationship of substitution, lifting?
