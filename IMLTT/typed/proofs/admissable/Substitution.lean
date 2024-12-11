import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import aesop

theorem substitution_univ_id : 
    .univ = substitute_zero .univ σ :=
  by
    rw [substitute_zero]
    rw [substitute]

/- # Substitution Property -/

theorem substitution :
  (∀ {n : Nat} {Γ' : Ctx (n + 2)} (isCtx : Γ' ctx)
    (Γ : Ctx n) (b B : Tm n) (A : Tm (n + 1)),
    Γ' = Γ ⬝ B ⬝ A → (Γ ⊢ b ∶ B)
    → Γ ⬝ substitute_zero A b ctx) ∧
  (∀ {n : Nat} {Γ' : Ctx (n + 1)} {A : Tm (n + 1)} (isType : Γ' ⊢ A type)
    (Γ : Ctx n) (b B : Tm n),
    Γ' = Γ ⬝ B → (Γ ⊢ b ∶ B)
    → Γ ⊢ (substitute_zero A b) type) ∧
  (∀ {n : Nat} {Γ' : Ctx (n + 1)} {A a : Tm (n + 1)} (hasType : Γ' ⊢ a ∶ A)
    (Γ : Ctx n) (b B : Tm n),
    Γ' = (Γ ⬝ B) → (Γ ⊢ b ∶ B)
    → Γ ⊢ (substitute_zero a b) ∶ (substitute_zero A b)) ∧
  (∀ {n : Nat} {Γ' : Ctx (n + 1)} {A A' : Tm (n + 1)} (isEqualType : Γ' ⊢ A ≡ A' type)
    (Γ : Ctx n) (b B : Tm n),
    Γ' = (Γ ⬝ B) → (Γ ⊢ b ∶ B)
    → Γ ⊢ (substitute_zero A b) ≡ (substitute_zero A' b) type) ∧
  (∀ {n : Nat} {Γ' : Ctx (n + 1)} {A a a' : Tm (n + 1)} (isEqualTerm : Γ' ⊢ a ≡ a' ∶ A)
    (Γ : Ctx n) (b B : Tm n),
    Γ' = Γ ⬝ B → (Γ ⊢ b ∶ B)
    → Γ ⊢ (substitute_zero a b) ≡ (substitute_zero a' b) ∶ (substitute_zero A b))
 :=
  by
    suffices h :
      (∀ {n : Nat} {Γ' : Ctx n}, Γ' ctx →
        ∀ (m : Nat) (Γ : Ctx m) (eqM : n = m + 2) (b B : Tm m) (A : Tm (m + 1)),
        eqM ▸ Γ' = Γ ⬝ B ⬝ A → (Γ ⊢ b ∶ B)
        → Γ ⬝ substitute_zero A b ctx) ∧
      (∀ {n : Nat} {Γ' : Ctx n} {A' : Tm n}, Γ' ⊢ A' type →
        ∀ (m : Nat) (Γ : Ctx m) (eqM : n = m + 1) (b B : Tm m) (A : Tm (m + 1)),
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ A' = A → (Γ ⊢ b ∶ B)
        → Γ ⊢ substitute_zero A b type) ∧
      (∀ {n : Nat} {Γ' : Ctx n} {A' a' : Tm n}, (Γ' ⊢ a' ∶ A') →
        ∀ (m : Nat) (Γ : Ctx m) (eqM : n = m + 1) (b B : Tm m) (a A : Tm (m + 1)),
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ a' = a → eqM ▸ A' = A → (Γ ⊢ b ∶ B)
        → Γ ⊢ substitute_zero a b ∶ substitute_zero A b) ∧
      (∀ {n : Nat} {Γ' : Ctx n} {C C' : Tm n}, Γ' ⊢ C ≡ C' type →
        ∀ (m : Nat) (Γ : Ctx m) (eqM : n = m + 1) (b B : Tm m) (A A' : Tm (m + 1)),
          eqM ▸ Γ' = Γ ⬝ B → eqM ▸ C = A → eqM ▸ C' = A' → (Γ ⊢ b ∶ B)
          → Γ ⊢ substitute_zero A b ≡ substitute_zero A' b type) ∧
      (∀ {n : Nat} {Γ' : Ctx n} {C c c' : Tm n}, (Γ' ⊢ c ≡ c' ∶ C) →
        ∀ (m : Nat) (Γ : Ctx m) (eqM : n = m + 1) (b B : Tm m) (a a' A : Tm (m + 1)),
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A → (Γ ⊢ b ∶ B)
        → Γ ⊢ substitute_zero a b ≡ substitute_zero a' b ∶ substitute_zero A b)
      by
        any_goals
          repeat' (apply And.intro)
        · intro n Γ' hIsCtx Γ b B A hΓeq hbB
          apply And.left h
          · apply hIsCtx
          · apply hΓeq
          · apply hbB
          · rfl
        · intro n Γ' A hIsType Γ b B hΓeq hbB
          apply And.left (And.right h)
          · apply hIsType
          · apply hΓeq
          · rfl
          · apply hbB
          · rfl
        · intro n Γ' A a hHasType Γ b B hΓeq hbB
          apply And.left (And.right (And.right h))
          · apply hHasType
          · apply hΓeq
          · rfl
          · rfl
          · apply hbB
          · rfl
        · intro n Γ' A A' hIsEqualType Γ b B hΓeq hbB
          apply And.left (And.right (And.right (And.right h)))
          · apply hIsEqualType
          · apply hΓeq
          · rfl
          · rfl
          · apply hbB
          · rfl
        · intro n Γ' A a a' hIsEqualTerm Γ b B hΓeq hbB
          apply And.right (And.right (And.right (And.right h)))
          · apply hIsEqualTerm
          · apply hΓeq
          · rfl
          · rfl
          · rfl
          · apply hbB
          · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m (Γ : Ctx m) (eqM : n = m + 2) b B A,
        eqM ▸ Γ' = Γ ⬝ B ⬝ A → (Γ ⊢ b ∶ B)
        → (Γ ⬝ (substitute_zero A b)) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m (Γ : Ctx m) (eqM : n = m + 1) b B A,
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ A' = A → (Γ ⊢ b ∶ B)
        → Γ ⊢ (substitute_zero A b) type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m (Γ : Ctx m) (eqM : n = m + 1) b B a A,
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ a' = a → eqM ▸ A' = A → (Γ ⊢ b ∶ B)
        → Γ ⊢ (substitute_zero a b) ∶ (substitute_zero A b))
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m (Γ : Ctx m) (eqM : n = m + 1) b B A A',
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ C = A → eqM ▸ C' = A' → (Γ ⊢ b ∶ B)
        → Γ ⊢ (substitute_zero A b) ≡ (substitute_zero A' b) type)
      (motive_5 := fun {n} Γ' c c' C _haaA => 
        ∀ m (Γ : Ctx m) (eqM : n = m + 1) b B a a' A,
        eqM ▸ Γ' = Γ ⬝ B → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A → (Γ ⊢ b ∶ B)
        → Γ ⊢ (substitute_zero a b) ≡ (substitute_zero a' b) ∶ (substitute_zero A b))
    case IsCtxEmpty =>
      intro m Γ eqM b B A heqM hbB
      simp [Nat.not_eq_zero_of_lt] at eqM
    case IsCtxExtend =>
      intro n Γ' A' hIsCtx hA' ihIsCtx ihIsType m Γ heqM b B A hCtxEq hbB
      apply IsCtx.extend
      · apply boundary_ctx_term hbB
      · cases heqM
        cases hCtxEq
        apply ihIsType
        · rfl
        · rfl
        · apply hbB
        · omega
    case IsTypeUnitForm =>
      intro n Γ' hIsCtx ihIsCtx
      intro m Γ heqM b B A hCtxEq h1Eq hbB
      apply ctx_extr
      cases heqM
      cases hCtxEq
      rw [substitute_zero] at *
      rw [←h1Eq] at *
      rw [substitute] at *
      apply IsCtx.extend
      · apply ctx_decr hIsCtx
      · apply IsType.unit_form (ctx_decr hIsCtx)
    case IsTypeEmptyForm =>
      intro n Γ' hIsCtx ihIsCtx
      intro m Γ heqM b B A hCtxEq h0Eq hbB
      apply ctx_extr
      cases heqM
      cases hCtxEq
      rw [substitute_zero] at *
      rw [←h0Eq] at *
      rw [substitute] at *
      apply IsCtx.extend
      · apply ctx_decr hIsCtx
      · apply IsType.empty_form (ctx_decr hIsCtx)
    case IsTypePiForm =>
      intro n Γ' A' B' hA hB ihA ihB
      intro m Γ heqM s S T hCtxEq hPieq hsS
      cases heqM
      rw [←hPieq]
      apply IsType.pi_form
      · apply ihA
        · apply hCtxEq
        · rfl
        · apply hsS
        · rfl
      · simp [lift_subst_n]
        have h := ihA m Γ rfl s S A' hCtxEq rfl hsS
        sorry
    case IsTypeSigmaForm =>
      intro n Γ' A' B' hA hB ihA ihB
      intro m Γ heqM s S T hCtxEq hSigmaEq hsS
      cases heqM
      rw [←hSigmaEq]
      apply IsType.sigma_form
      · apply ihA
        · apply hCtxEq
        · rfl
        · apply hsS
        · rfl
      · simp [lift_subst_n]
        sorry
    case IsTypeIdenForm =>
      intro n Γ' c C c' hcC hcC' ihcC ihcC'
      intro m Γ heqM b B A hCtxEq hIdEq hbB
      cases heqM
      rw [←hIdEq]
      apply IsType.iden_form
      · apply ihcC
        · apply hCtxEq
        · rfl
        · rfl
        · apply hbB
        · rfl
      · apply ihcC'
        · apply hCtxEq
        · rfl
        · rfl
        · apply hbB
        · rfl
    case IsTypeUnivForm =>
      intro n Γ' hIsCtx ihIsCtx
      intro m Γ heqM b B A hCtxEq h0Eq hbB
      apply ctx_extr
      cases heqM
      cases hCtxEq
      rw [substitute_zero] at *
      rw [←h0Eq] at *
      rw [substitute] at *
      apply IsCtx.extend
      · apply ctx_decr hIsCtx
      · apply IsType.univ_form (ctx_decr hIsCtx)
    case IsTypeUnivElim =>
      intro n Γ' A' hAU ihAU
      intro m Γ heqM b B A hCtxEq hAEq hbB
      cases heqM
      apply IsType.univ_elim
      rw [substitution_univ_id]
      apply ihAU
      · apply hCtxEq
      · apply hAEq
      · rfl
      · apply hbB
      · rfl
    any_goals sorry

theorem substitution_ctx : HasType Γ b B → IsCtx (Γ ⬝ B ⬝ A)
                           → IsCtx (Γ ⬝ (substitute_zero A b)) :=
  by
    intro hbB hiCBA
    apply And.left substitution
    · apply hiCBA
    · rfl
    · apply hbB

theorem substitution_type : HasType Γ b B → IsType (Γ ⬝ B) A 
                            → IsType Γ (substitute_zero A b) :=
  by
    intro hbB hA
    apply And.left (And.right substitution)
    · apply hA
    · rfl
    · apply hbB

theorem substitution_term : HasType Γ b B → HasType (Γ ⬝ B) a A
                            → HasType Γ (substitute_zero a b) (substitute_zero A b) :=
  by
    intro hbB haA
    apply And.left (And.right (And.right substitution))
    · apply haA
    · rfl
    · apply hbB

theorem substitution_type_eq : HasType Γ b B → IsEqualType (Γ ⬝ B) A A'
                               → IsEqualType Γ (substitute_zero A b) (substitute_zero A' b) :=
  by
    intro hbB hAA
    apply And.left (And.right (And.right (And.right substitution)))
    · apply hAA
    · rfl
    · apply hbB


theorem substitution_term_eq : HasType Γ b B → IsEqualTerm (Γ ⬝ B) a a' A
                               → IsEqualTerm Γ (substitute_zero a b) (substitute_zero a' b) 
                                 (substitute_zero A b) :=
  by
    intro hbB haaA
    apply And.right (And.right (And.right (And.right substitution)))
    · apply haaA
    · rfl
    · apply hbB

-- helper

theorem substitution_inv_type : B' = (substitute_zero B a) → IsType Γ B'
                                → HasType Γ a A
                                → IsType (Γ ⬝ A) B :=
  by
    intro hBeqB' hBs haA
    match hBs with
    | .unit_form hiC => sorry
    | _ => sorry

theorem substitution_inv_type_eq : B' = (substitute_zero B a) → C' = (substitute_zero C a) 
                                → IsEqualType Γ B' C'
                                → HasType Γ a A
                                → IsEqualType (Γ ⬝ A) B C :=
  by
    sorry

-- B⌈Subst.weak id, a, a', p⌉ type
theorem substitution_separate_test :
  (substitute A (.weak .id, s1, s2, s3))
  = (substitute (substitute_zero A (weaken s3 (.shift (.shift .id)))) (.weak .id, s1, s2)) :=
  by
    simp [substitute_zero]
    sorry

-- FIXME: try to find generalized form, think substitution algebra

theorem substitution_separate_degeneralized : -- TODO: is this provable?
  (substitute A (.weak .id, s1, s2, s3))
  = substitute_zero
      (substitute_zero
        (substitute_zero A (weaken s3 (.shift (.shift .id))))
      (weaken s2 (.shift .id)))
    s1 :=
  by
    simp [substitute_zero]
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
