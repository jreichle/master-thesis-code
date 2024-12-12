import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem og_weak : HasType Γ (.var i) A → IsType Γ B
                  → HasType (Γ ⬝ B) (.var (.succ i)) (weaken (.shift .id) A) :=
  by
    intro hiA hB
    match hB with
    | a => sorry

theorem weakening :
  (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → ∀ (B A : Tm n), Γ ⬝ A ctx → Γ ⊢ B type 
    → Γ ⬝ B ⬝ weaken Weak.id.shift A ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken Weak.id.shift A type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken Weak.id.shift a ∶ weaken Weak.id.shift A) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken Weak.id.shift A ≡ weaken  Weak.id.shift A' type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → ∀ (B : Tm n), Γ ⊢ B type 
    → Γ ⬝ B ⊢ weaken Weak.id.shift a ≡ weaken Weak.id.shift a' ∶ weaken Weak.id.shift A) :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC =>
        ∀B, ∀ A, Γ ⬝ A ctx → Γ ⊢ B type
        → Γ ⬝ B ⬝ (weaken (.shift .id) A) ctx)
      (motive_2 := fun Γ A _hA =>
        ∀B, Γ ⊢ B type
        → Γ ⬝ B ⊢ (weaken (.shift .id) A) type)
      (motive_3 := fun Γ a A haA =>
        ∀B, Γ ⊢ B type
        → HasType (Γ ⬝ B) (weaken (.shift .id) a) (weaken (.shift .id) A))
      (motive_4 := fun Γ A A' _hAA =>
        ∀B, Γ ⊢ B type
        → Γ ⬝ B ⊢ (weaken (.shift .id) A) ≡ (weaken (.shift .id) A') type)
      (motive_5 := fun Γ a a' A _haaA =>
        ∀B, Γ ⊢ B type
        → Γ ⬝ B ⊢ (weaken (.shift .id) a) ≡ (weaken (.shift .id) a') ∶ (weaken (.shift .id)) A)
    case IsCtxEmpty =>
      -- ⊢ ∀ (B A : Tm 0), ε ⬝ A ctx → ε ⊢ B type → ε ⬝ B ⬝ (A⌊↑id⌋) ctx
      intro B A hiA hB
      apply IsCtx.extend
      have hiB := IsCtx.extend IsCtx.empty hB
      have hA := ctx_extr hiA
      · apply hiB
      · sorry
    any_goals sorry

theorem weakening_ctx : IsCtx (Γ ⬝ A) → IsType Γ B
                        → IsCtx (Γ ⬝ B ⬝ (weaken (.shift .id) A)) :=
  by
    intro hiCA hB
    apply And.left weakening
    · apply ctx_decr hiCA
    · apply hiCA
    · apply hB

theorem weakening_type : IsType Γ A → IsType Γ B
                         → IsType (Γ ⬝ B) (weaken (.shift .id) A) :=
  by
    intro hA hB
    apply And.left (And.right weakening)
    · apply hA
    · apply hB


theorem weakening_term : HasType Γ a A → IsType Γ B
                         → HasType (Γ ⬝ B) (weaken (.shift .id) a) 
                           (weaken (.shift .id) A) :=
  by
    intro haA hB
    apply And.left (And.right (And.right weakening))
    · apply haA
    · apply hB

theorem weakening_type_eq : IsEqualType Γ A A' → IsType Γ B
                            → IsEqualType (Γ ⬝ B) (weaken (.shift .id) A)
                              (weaken (.shift .id) A') :=
  by
    intro hAA hB
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · apply hB

theorem weakening_term_eq : IsEqualTerm Γ a a' A → IsType Γ B
                            → IsEqualTerm (Γ ⬝ B) (weaken (.shift .id) a)
                              (weaken (.shift .id) a')
                              (weaken (.shift .id) A) :=
  by
    intro haaA hB
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · apply hB
