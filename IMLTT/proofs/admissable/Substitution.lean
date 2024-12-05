import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.proofs.boundary.BoundaryIsCtx

import IMLTT.proofs.Recursor

import aesop

/- # Substitution Property -/

theorem nat_decr_eq {m n l : Nat} : 
    m + l = n + l → m = n :=
  by
    intro h
    match l with
    | 0 => 
      simp [] at *
      apply h
    | i + 1 =>
      simp [←Nat.add_assoc] at *
      apply nat_decr_eq h

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
    case IsTypeEmptyForm =>
      intro n Γ' hIsCtx ihIsCtx m Γ heqM b B A hCtxEq h0Eq hbB
      apply ctx_extr -- TODO: use fact that A = empty and substitution doesn't change empty
      cases heqM
      rw [substitute_zero] at *
      rw [←h0Eq] at *
      rw [substitute] at *
      sorry
    any_goals sorry

#check Eq.symm
#check cast
#check congrArg

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
