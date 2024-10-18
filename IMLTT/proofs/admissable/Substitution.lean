import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

/- # Substitution Property -/

theorem substitution_ctx : HasType Γ a A → IsCtx (Γ ⬝ A ⬝ B)
                           → IsCtx (Γ ⬝ (substitute_zero B a)) :=
  sorry

theorem substitution_type : HasType Γ a A → IsType (Γ ⬝ A) B 
                            → IsType Γ (substitute_zero B a) :=
  sorry

theorem substitution_term : HasType Γ a A → HasType (Γ ⬝ A) b B
                            → HasType Γ (substitute_zero b A) (substitute_zero B A) :=
  sorry

theorem substitution_type_eq : HasType Γ a A → IsEqualType (Γ ⬝ A) B B'
                               → IsEqualType Γ (substitute_zero B a) (substitute_zero B' a) :=
  sorry

theorem substitution_term_eq : HasType Γ a A → IsEqualTerm (Γ ⬝ A) b b' B
                               → IsEqualTerm Γ (substitute_zero b a) (substitute_zero b' a) 
                                 (substitute_zero B a) :=
  sorry

/- # Substitution inverse -/

theorem nat_not_less_than_zero : ¬ (i < 0) :=
  by
    apply Nat.not_succ_le_zero

-- theorem substitution_eq_inverse : A = weaken (substitute_zero (substitute_zero A (.var 0)) (.var 0)) 
--                                       (.shift (.shift .id)) :=
--   by
--     induction A with
--     | unit =>
--       simp [substitute]
--     | pi A B ihA ihB =>
--       simp [substitute]
--       simp [lift]
--       apply And.intro
--       · apply ihA
--       sorry
--     | var n => sorry
--     | _ => sorry

-- theorem substitute_type_eq_inverse : IsEqualType Γ A A' 
--                                      = IsEqualType Γ (substitute (substitute A (.var i) j) j i)
--                                        (substitute (substitute A' i j) j i) :=
--   by
--     sorry

-- theorem substitution_id_lift : (substitute A (Tm.var i) i) = A :=
--   by
--     sorry
--   --   induction A generalizing i with
--   --   | unit =>
--   --     rw [substitute]
--   --     rw [lift]
--   --   | empty =>
--   --     rw [substitute]
--   --     rw [lift]
--   --   | pi A B ihA ihB =>
--   --     rw [substitute]
--   --     rw [lift]
--   --     rw [ihA]
--   --     rw [←ihB]
--   --     rw [lift]
--   --     simp [nat_not_less_than_zero]
--   --   | sigma A B ihA ihB =>
--   --     rw [substitute]
--   --     rw [lift]
--   --     rw [ihA]
--   --     rw [←ihB]
--   --     rw [lift]
--   --     simp [nat_not_less_than_zero]
--   --   | var n =>
--   --     rw [substitute]
--   --     cases i with
--   --     | zero => 
--   --       simp [nat_not_less_than_zero]
--   --       cases n with
--   --       | zero =>
--   --         simp []
--   --         simp [lift]
--   --       | succ n' =>
--   --         simp []
--   --         simp [lift]
--   --     | succ i' =>
--   --       sorry
--   --   | _ => sorry
