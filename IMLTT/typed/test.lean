mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | next : Odd i → Even (i + 1)
  
  inductive Odd : Nat → Prop where
    | odd : Even i → Odd (i + 1)
end

set_option pp.proofs true

--      (motive_1 := fun Γ _hiC => IsCtx Γ)
--      (motive_2 := fun Γ _A _hA => IsCtx Γ)
--      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
--      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
--      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)

theorem test : ∀ {motive_1 : (a : Nat) → Even a → Prop} 
                 {motive_2 : (a : Nat) → Odd a → Prop} {a : Nat} (t : Even a) (t' : Odd b),
  motive_1 0 Even.zero →
  (∀ {i : Nat} (a : Odd i), motive_2 i a → motive_1 (i + 1) (Even.next a)) →
  (∀ {i : Nat} (a : Even i), motive_1 i a → motive_2 (i + 1) (Odd.odd a)) →
  motive_1 a t ∧ motive_2 b t'
 :=
  by
    intro m1 m2 a t t' hzero hnext hodd
    apply And.intro
    · refine' Even.recOn t (motive_1 := m1) (motive_2 := m2) hzero hnext hodd
    · apply Odd.recOn t' (motive_1 := m1) (motive_2 := m2) hzero hnext hodd


