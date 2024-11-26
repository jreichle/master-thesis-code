import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.proofs.Recursor

/- # Substitution Property -/


-- (∀ {n : Nat} {Γ : Ctx n} (isCtx : Γ ctx) (Γ_1 : Ctx a✝) (b B : Tm a✝),
--     (?m.308 Γ isCtx Γ_1 b B → Γ ctx) = (Γ_1 ⬝ B ⬝ A ctx) →
--       (Γ_1 ⊢ b ∶ B) → Γ_1 ⬝ substitute_zero A b ctx) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A_1 : Tm n} (isType : Γ ⊢ A_1 type) (Γ_1 : Ctx a✝) (b B : Tm a✝),
--       (?m.376 Γ A_1 isType Γ_1 b B → Γ ⊢ A_1 type) = (Γ_1 ⬝ B ⊢ A type) →
--         (Γ_1 ⊢ b ∶ B) → Γ_1 ⊢ substitute_zero A b type) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n} (hasType : Γ ⊢ a ∶ A) (Γ_1 : Ctx (?m.454 Γ a A hasType))
--         (b B : Tm (?m.454 Γ a A hasType)) (a_1 A_1 : Tm (?m.454 Γ a A hasType + 1)),
--         (Γ ⊢ a ∶ A) = (Γ_1 ⬝ B ⊢ a_1 ∶ A_1) →
--           (Γ_1 ⊢ b ∶ B) → Γ_1 ⊢ substitute_zero a_1 b ∶ substitute_zero A_1 b) ∧
--       (∀ {n : Nat} {Γ : Ctx n} {A A'_1 : Tm n} (isEqualType : Γ ⊢ A ≡ A'_1 type) (Γ_1 : Ctx a✝)
--           (b B : Tm a✝) (A_1 : Tm (a✝ + 1)),
--           (?m.538 Γ A A'_1 isEqualType Γ_1 b B A_1 → Γ ⊢ A ≡ A'_1 type) =
--               (Γ_1 ⬝ B ⊢ A_1 ≡ A' type) →
--             (Γ_1 ⊢ b ∶ B) → Γ_1 ⊢ substitute_zero A_1 b ≡ substitute_zero A' b type) ∧
--         ∀ {n : Nat} {Γ : Ctx n} {A_1 a a' : Tm n} (isEqualTerm : Γ ⊢ a ≡ a' ∶ A_1) (Γ_1 : Ctx a✝)
--           (b B : Tm a✝) (a_1 a'_1 : Tm (a✝ + 1)),
--           ?m.632 Γ a a' A_1 isEqualTerm Γ_1 b B a_1 a'_1 →
--             (Γ ⊢ a ≡ a' ∶ A_1) = (Γ_1 ⬝ B ⊢ a_1 ≡ a'_1 ∶ A) →
--               (Γ_1 ⊢ b ∶ B) →
--                 Γ_1 ⊢ substitute_zero a_1 b ≡ substitute_zero a'_1 b ∶ substitute_zero A b


--   (∀ {n : Nat} {Γ' : Ctx (n)} (isCtx : Γ' ctx), n > 1
--     → ∀ (Γ : Ctx (n - 2)) (b B : Tm (n - 2)) (A : Tm (n - 1)), Γ' ctx = (Γ ⬝ B ⬝ A ctx) → (Γ ⊢ b ∶ B)
--     → Γ ⬝ substitute_zero A b ctx) ∧
--   (∀ {n : Nat} {Γ' : Ctx n} {A : Tm n} (isType : Γ' ⊢ A type), n > 0
--     → ∀(Γ : Ctx (n - 1)) (b B : Tm (n - 1)), (Γ' ⊢ A type) = (Γ ⬝ B ⊢ A type)
--     → (Γ ⊢ b ∶ B) → Γ ⊢ substitute_zero A b type) ∧
--   (∀ {n : Nat} {Γ' : Ctx n} {A a : Tm n} (hasType : Γ' ⊢ a ∶ A), n > 0
--     → ∀ (Γ : Ctx (n - 1)) (b B : Tm (n - 1)), (Γ' ⊢ a ∶ A) = (Γ ⬝ B ⊢ a ∶ A)
--     → (Γ ⊢ b ∶ B) → Γ ⊢ substitute_zero a b ∶ substitute_zero A b) ∧
--   (∀ {n : Nat} {Γ' : Ctx n} {A A' : Tm n} (isEqualType : Γ' ⊢ A ≡ A' type), n > 0
--     → ∀ (Γ : Ctx (n - 1)) (b B : Tm (n - 1)), (Γ' ⊢ A ≡ A' type) = (Γ ⬝ B ⊢ A ≡ A' type) → (Γ ⊢ b ∶ B)
--     → Γ ⊢ substitute_zero A b ≡ substitute_zero A' b type) ∧
--   (∀ {n : Nat} {Γ' : Ctx n} {A a a' : Tm n} (isEqualTerm : Γ' ⊢ a ≡ a' ∶ A), n > 0
--     → ∀ (Γ : Ctx (n - 1)) (b B : Tm (n - 1)), (Γ' ⊢ a ≡ a' ∶ A) = (Γ ⬝ B ⊢ a ≡ a' ∶ A) → (Γ ⊢ b ∶ B)
--     → Γ ⊢ substitute_zero a b ≡ substitute_zero a' b ∶ substitute_zero A b)

-- set_option autoImplicit false

-- theorem substitution : -- FIXME: Γ' cannot be n+2
--   IsCtx (Γ ⬝ B ⬝ A) → HasType Γ b B → IsCtx (Γ ⬝ (substitute_zero A b)) ∧
--   IsType (Γ ⬝ B) A  → HasType Γ b B → IsType Γ (substitute_zero A b) ∧
--   HasType (Γ ⬝ B) a A → HasType Γ b B → HasType Γ (substitute_zero a b) (substitute_zero A b) ∧
--   IsEqualType (Γ ⬝ B) A A' → HasType Γ b B
--     → IsEqualType Γ (substitute_zero A b) (substitute_zero A' b) ∧
--   IsEqualTerm (Γ ⬝ B) a a' A → HasType Γ b B
--     → IsEqualTerm Γ (substitute_zero a b) (substitute_zero a' b) (substitute_zero A b)
--   :=
--   by
--     apply judgment_recursor
--       (motive_1 := fun Γ' _hiC =>
--         ∀ Γ, ∀ b, ∀ B, ∀ A, Γ' ctx = (Γ ⬝ B ⬝ A ctx) → (Γ ⊢ b ∶ B)
--         → (Γ ⬝ (substitute_zero A b)) ctx)
--       (motive_2 := fun Γ' A' _hA =>
--         ∀ Γ, ∀ b, ∀ B, ∀ A, Γ' ⊢ A' type = (Γ ⬝ B ⊢ A type) → (Γ ⊢ b ∶ B)
--         → Γ ⊢ (substitute_zero A b) type)
--       (motive_3 := fun Γ' a' A' haA =>
--         ∀ Γ, ∀ b, ∀ B, ∀ a, ∀ A, (Γ' ⊢ a' ∶ A') = ((Γ ⬝ B) ⊢ a ∶ A) → (Γ ⊢ b ∶ B)
--         → Γ ⊢ (substitute_zero a b) ∶ (substitute_zero A b))
--       (motive_4 := fun Γ' C C' _hCC =>
--         ∀ Γ, ∀ b, ∀ B, ∀ A, ∀ A', Γ' ⊢ C ≡ C' type = (Γ ⬝ B ⊢ A ≡ A' type) → (Γ ⊢ b ∶ B)
--         → Γ ⊢ (substitute_zero A b) ≡ (substitute_zero A' b) type)
--       (motive_5 := fun Γ' c c' C _haaA =>
--         ∀ Γ, ∀ b, ∀ B, ∀ a, ∀ a', ∀ A', (Γ' ⊢ c ≡ c' ∶ C) = (Γ ⬝ B ⊢ a ≡ a' ∶ A) → (Γ ⊢ b ∶ B)
--         → Γ ⊢ (substitute_zero a b) ≡ (substitute_zero a' b) ∶ (substitute_zero A b))
--     any_goals sorry

theorem substitution_ctx : HasType Γ b B → IsCtx (Γ ⬝ B ⬝ A)
                           → IsCtx (Γ ⬝ (substitute_zero A b)) :=
  sorry

theorem substitution_type : HasType Γ b B → IsType (Γ ⬝ B) A 
                            → IsType Γ (substitute_zero A b) :=
  by
    intro haA hB
    sorry -- TODO: recursor

theorem substitution_term : HasType Γ b B → HasType (Γ ⬝ B) a A
                            → HasType Γ (substitute_zero a b) (substitute_zero A b) :=
  sorry

theorem substitution_type_eq : HasType Γ b B → IsEqualType (Γ ⬝ B) A A'
                               → IsEqualType Γ (substitute_zero A b) (substitute_zero A' b) :=
  sorry

theorem substitution_term_eq : HasType Γ b B → IsEqualTerm (Γ ⬝ B) a a' A
                               → IsEqualTerm Γ (substitute_zero a b) (substitute_zero a' b) 
                                 (substitute_zero A b) :=
  sorry

theorem substitution_zero_n : -- FIXME: matching problem on rhs
  IsType Γ (substitute A (σ, a)) = IsType Γ A := -- IsType Γ (substitute (substitute_zero A a) σ) :=
  -- FIXME: is this even correct
  sorry

theorem substitution_inv_type : B' = (substitute_zero B a) → IsType Γ B'
                                → HasType Γ a A
                                → IsType (Γ ⬝ A) B :=
  by
    intro hBeqB' hBs haA
    match hBs with
    | .unit_form hiC => sorry
    | _ => sorry

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
