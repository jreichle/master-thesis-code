import IMLTT.typed.JudgmentsAndRules

set_option pp.proofs true

-- FIXME: macht des überhaupt Sinn? -- why not

theorem judgment_recursor :
  ∀ {motive_1 : {n : Nat} → (Γ : Ctx n) → IsCtx Γ → Prop}
    {motive_2 : {n : Nat} → (Γ : Ctx n) → (A : Tm n) → IsType Γ A → Prop}
    {motive_3 : {n : Nat} → (Γ : Ctx n) → (a A : Tm n) → HasType Γ a A → Prop}
    {motive_4 : {n : Nat} → (Γ : Ctx n) → (A A' : Tm n) → IsEqualType Γ A A' → Prop}
    {motive_5 : {n : Nat} → (Γ : Ctx n) → (a a' A : Tm n) → IsEqualTerm Γ a a' A → Prop}
    {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n}
    (isCtx : IsCtx Γ)
    (isType : IsType Γ A)
    (hasType : HasType Γ a A)
    (isEqualType : IsEqualType Γ A A')
    (isEqualTerm : IsEqualTerm Γ a a' A),
    -- FIXME: here all cases :(
    motive_1 Γ isCtx ∧ motive_2 Γ A isType ∧ motive_3 Γ a A hasType 
    ∧ motive_4 Γ A A' isEqualType ∧ motive_5 Γ a a' A isEqualTerm
  :=
  by
    intro m1 m2 m3 m4 m5 n Γ A A' a a' hiC hA haA hAA haaA
    any_goals repeat' apply And.intro
    · apply IsCtx.recOn
        (motive_1 := m1) (motive_2 := m2) (motive_3 := m3) (motive_4 := m4) (motive_5 := m5)
        hiC -- here all cases
      any_goals sorry
    · sorry
    · sorry
    · sorry
    · sorry

theorem test : IsType Γ A → IsEqualType Γ A A :=
  by
  intro hA
  apply judgment_recursor
    (motive_1 := fun Γ _hiC => IsCtx Γ)
    (motive_2 := fun Γ A _hA => IsEqualType Γ A A)
    (motive_3 := fun Γ a A _haA => IsEqualTerm Γ a a A)
    (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
    (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
    sorry  -- need isCtx here but don't want that
    -- hA
    --
theorem boundary_ctx_term : IsCtx Γ ∨ IsType Γ A ∨ HasType Γ a A
                            ∨ IsEqualType Γ A A' ∨ IsEqualTerm Γ a a' A
                            → IsCtx Γ :=
  by
    intro haA
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ _A _hA => IsCtx Γ)
      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
      haA

mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | next : Odd i → Even (i + 1)
 
  inductive Odd : Nat → Prop where
    | odd : Even i → Odd (i + 1)
end

theorem test : 
  ∀ {motive_1 : (a : Nat) → Even a → Prop} 
    {motive_2 : (a : Nat) → Odd a → Prop} 
    {a : Nat} (t : Even a) (t' : Odd b),
  motive_1 0 Even.zero →
  (∀ {i : Nat} (a : Odd i), motive_2 i a → motive_1 (i + 1) (Even.next a)) →
  (∀ {i : Nat} (a : Even i), motive_1 i a → motive_2 (i + 1) (Odd.odd a)) →
  motive_1 a t ∧ motive_2 b t'
 :=
  by
    intro m1 m2 a t t' hzero hnext hodd
    apply And.intro
    · apply Even.recOn (motive_1 := m1) (motive_2 := m2) t  hzero hnext hodd
    · apply Odd.recOn (motive_1 := m1) (motive_2 := m2) t' hzero hnext hodd


