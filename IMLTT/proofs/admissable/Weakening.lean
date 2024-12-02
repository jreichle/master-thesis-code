import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.proofs.Recursor
import IMLTT.proofs.boundary.BoundaryIsCtx

theorem og_weak : HasType Γ (.var i) A → IsType Γ B
                  → HasType (Γ ⬝ B) (.var (.succ i)) (weaken A (.shift .id)) :=
  by
    intro hiA hB
    match hB with
    | a => sorry

theorem weakening :
  (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → ∀ (B A : Tm n), Γ ⬝ A ctx → Γ ⊢ B type 
    → Γ ⬝ B ⬝ weaken A Weak.id.shift ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken A Weak.id.shift type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken a Weak.id.shift ∶ weaken A Weak.id.shift) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken A Weak.id.shift ≡ weaken A' Weak.id.shift type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken a Weak.id.shift ≡ weaken a' Weak.id.shift ∶ weaken A Weak.id.shift) :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC =>
        ∀B, ∀ A, Γ ⬝ A ctx → Γ ⊢ B type
        → Γ ⬝ B ⬝ (weaken A (.shift .id)) ctx)
      (motive_2 := fun Γ A _hA =>
        ∀B, Γ ⊢ B type
        → Γ ⬝ B ⊢ (weaken A (.shift .id)) type)
      (motive_3 := fun Γ a A haA =>
        ∀B, Γ ⊢ B type
        → HasType (Γ ⬝ B) (weaken a (.shift .id)) (weaken A (.shift .id)))
      (motive_4 := fun Γ A A' _hAA =>
        ∀B, Γ ⊢ B type
        → Γ ⬝ B ⊢ (weaken A (.shift .id)) ≡ (weaken A' (.shift .id)) type)
      (motive_5 := fun Γ a a' A _haaA =>
        ∀B, Γ ⊢ B type
        → Γ ⬝ B ⊢ (weaken a (.shift .id)) ≡ (weaken a' (.shift .id)) ∶ (weaken A (.shift .id)))
    sorry

theorem weakening_ctx : IsCtx (Γ ⬝ A) → IsType Γ B
                        → IsCtx (Γ ⬝ B ⬝ (weaken A (.shift .id))) :=
  by
    intro hiCA hB
    apply And.left weakening
    · apply ctx_decr hiCA
    · apply hiCA
    · apply hB

theorem weakening_type : IsType Γ A → IsType Γ B
                         → IsType (Γ ⬝ B) (weaken A (.shift .id)) :=
  by
    intro hA hB
    apply And.left (And.right weakening)
    · apply hA
    · apply hB


theorem weakening_term : HasType Γ a A → IsType Γ B
                         → HasType (Γ ⬝ B) (weaken a (.shift .id)) 
                           (weaken A (.shift .id)) :=
  by
    intro haA hB
    apply And.left (And.right (And.right weakening))
    · apply haA
    · apply hB

theorem weakening_type_eq : IsEqualType Γ A A' → IsType Γ B
                            → IsEqualType (Γ ⬝ B) (weaken A (.shift .id)) 
                              (weaken A' (.shift .id)) :=
  by
    intro hAA hB
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · apply hB

theorem weakening_term_eq : IsEqualTerm Γ a a' A → IsType Γ B
                            → IsEqualTerm (Γ ⬝ B) (weaken a (.shift .id)) 
                              (weaken a' (.shift .id))
                              (weaken A (.shift .id)) :=
  by
    intro haaA hB
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · apply hB

-- algebra?


#reduce ((Tm.pi : Tm 1 → Tm 2 → Tm 1) v(0) v(1))⌊.shift .id⌋
#reduce ((Tm.pi : Tm 1 → Tm 2 → Tm 1) v(0) v(1))⌊.shift (.shift .id)⌋
#reduce ((Tm.pi : Tm 1 → Tm 2 → Tm 1) v(0) v(1))⌊(.shift .id)⌋⌊.shift .id⌋
#reduce ((Tm.refl : Tm 1 → Tm 1 → Tm 1) v(0) v(1))⌊.shift .id⌋
#reduce ((Tm.refl : Tm 1 → Tm 1 → Tm 1) v(0) v(1))⌊.shift (.shift .id)⌋
#reduce ((Tm.refl : Tm 1 → Tm 1 → Tm 1) v(0) v(1))⌊.shift .id⌋⌊.shift .id⌋

-- | .shift γ => .shift (comp_weaken γ ρ')

theorem weakening_shift_test {ρ : Weak m n} :
  .shift ρ = .shift .id ∘ ρ :=
  by
    simp [comp_weaken]

-- B⌊⇑↑ρ⌋ = B⌊⇑ρ⌋⌊⇑↑id⌋
theorem weakening_lift_shift {S : Tm (n + 1)} {ρ : Weak m n} :
    S⌊.lift (.shift ρ)⌋ = S⌊.lift ρ⌋⌊.lift (.shift .id)⌋ :=
  by
    match S with
    | .unit => 
      simp [weaken]
    | .empty => 
      simp [weaken]
    | .pi A B => 
      simp [weaken]
      apply And.intro
      · apply weakening_lift_shift
      · simp [lift_weak_n]
        sorry
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_lift_shift
      · sorry
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_lift_shift
      · apply And.intro
        · apply weakening_lift_shift
        · apply weakening_lift_shift
    | .univ =>
      simp [weaken]
    | .var i =>
      simp [weaken]
      simp [weaken_var]
      sorry
      -- match i with
      -- | ⟨0, _⟩ => sorry
      -- | ⟨x' + 1, h⟩ => sorry
    | .tt =>
      simp [weaken]
    | .indUnit A b a =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .indEmpty A b =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .lam A b =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .app f a => sorry
    | .pairSigma a b => sorry
    | .indSigma A B C c p =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .refl A a => sorry
    | .j A B b a a' p =>
      simp [weaken]
      simp [lift_weak_n]
      sorry

theorem weakening_shift {S : Tm n} {ρ : Weak m n} : 
    S⌊.shift ρ⌋ = S⌊ρ⌋⌊.shift .id⌋ :=
  by
    match S with
    | .unit => 
      simp [weaken]
    | .empty => 
      simp [weaken]
    | .pi A B => 
      simp [weaken]
      apply And.intro
      · apply weakening_shift
      · simp [lift_weak_n]
        sorry
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_shift
      · sorry
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_shift
      · apply And.intro
        · apply weakening_shift
        · apply weakening_shift
    | .univ =>
      simp [weaken]
    | .var i =>
      simp [weaken]
      simp [weaken_var]
    | .tt =>
      simp [weaken]
    | .indUnit A b a =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .indEmpty A b =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .lam A b =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .app f a => sorry
    | .pairSigma a b => sorry
    | .indSigma A B C c p =>
      simp [weaken]
      simp [lift_weak_n]
      sorry
    | .refl A a => sorry
    | .j A B b a a' p =>
      simp [weaken]
      simp [lift_weak_n]
      sorry

theorem weakening_shift_double {S : Tm n} {ρ : Weak m n} : 
    S⌊.shift (.shift ρ)⌋ = S⌊.shift ρ⌋⌊.shift .id⌋ :=
  by
    rw [weakening_shift]

theorem weakening_comp_shift {S : Tm n} {ρ : Weak m n} :
    S⌊.shift .id ∘ ρ⌋ = S⌊ρ⌋⌊.shift .id⌋ :=
  by
    simp [comp_weaken]
    apply weakening_shift
