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
    any_goals sorry

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
