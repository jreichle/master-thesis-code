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

theorem nat_not_less_than_zero : ¬ (i < 0) :=
  by
    apply Nat.not_succ_le_zero

theorem substitution_var_eq_inverse :
    Tm.var (n - 2) = (substitute (substitute (Tm.var n) (Tm.var 0) 0) (Tm.var 0) 0) :=
  by
    induction n with
    | zero =>
      simp [substitute]
    | succ n' ihj =>
      simp [substitute]
      simp [nat_not_less_than_zero]
      cases n' with
      | zero =>
        simp [lift]
      | succ n'' =>
        simp []

-- FIXME: not doable with current meta operations
theorem substitution_eq_inverse : A = (substitute (substitute A (Tm.var 0) 0) 0 0) :=
  by
    induction A with
    | unit =>
      simp [substitute]
    | pi A B ihA ihB =>
      simp [substitute]
      simp [lift]
      apply And.intro
      · apply ihA
      sorry
    | var n => sorry
    | _ => sorry

theorem substitute_type_eq_inverse : IsEqualType Γ A A' 
                                     = IsEqualType Γ (substitute (substitute A (Tm.var i) j) j i)
                                       (substitute (substitute A' i j) j i) :=
  by
    sorry

theorem substitution_id_lift : (substitute A (Tm.var i) i) = A := -- FIXME: -1?
  by
    sorry
  --   induction A generalizing i with
  --   | unit =>
  --     rw [substitute]
  --     rw [lift]
  --   | empty =>
  --     rw [substitute]
  --     rw [lift]
  --   | pi A B ihA ihB =>
  --     rw [substitute]
  --     rw [lift]
  --     rw [ihA]
  --     rw [←ihB]
  --     rw [lift]
  --     simp [nat_not_less_than_zero]
  --   | sigma A B ihA ihB =>
  --     rw [substitute]
  --     rw [lift]
  --     rw [ihA]
  --     rw [←ihB]
  --     rw [lift]
  --     simp [nat_not_less_than_zero]
  --   | var n =>
  --     rw [substitute]
  --     cases i with
  --     | zero => 
  --       simp [nat_not_less_than_zero]
  --       cases n with
  --       | zero =>
  --         simp []
  --         simp [lift]
  --       | succ n' =>
  --         simp []
  --         simp [lift]
  --     | succ i' =>
  --       sorry
  --   | _ => sorry
