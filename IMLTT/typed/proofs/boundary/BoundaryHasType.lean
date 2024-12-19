import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.DefeqSymm

theorem boundary_has_type :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, (Γ ⊢ A type) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ a ∶ A) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, (Γ ⊢ A ≡ A' type) → Γ ⊢ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ∶ A) :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ a A _haA => HasType Γ a A)
      (motive_4 := fun Γ A A' _hAA => IsType Γ A)
      (motive_5 := fun Γ a a' A _haaA => HasType Γ a A)
    case IsEqualTermUnitComp =>
      intro n Γ A a S hA haA hEq _ _
      apply HasType.unit_elim hA haA (HasType.unit_intro (boundary_ctx_term haA)) hEq
    case IsEqualTermSigmaComp =>
      intro n Γ a A b B C s S c haA hbB hC hcC hEqs hEqS ihaA ihbB ihC ihcC
      apply HasType.sigma_elim
      · apply HasType.sigma_intro haA hbB
      · apply ihC
      · apply hcC
      · apply hEqS
    case IsEqualTermIdenComp =>
      intro n Γ A B b a S hB hbB haA hEq ihB ihbB ihaA
      apply HasType.iden_elim
      · apply hB
      · apply hbB
      · apply HasType.iden_intro ihaA
      · apply hEq
    case IsEqualTypeIdenFormEq =>
      intro n Γ A A' a₁ a₂ a₃ a₄
      intro hAA _haaA _haaA' _ihAA ihaaA ihaaA'
      apply IsType.iden_form
      · apply ihaaA
      · apply HasType.ty_conv ihaaA' (defeq_symm_type hAA)
    any_goals
      solve
      | repeat'
        first
        | intro a
        | aesop

theorem boundary_is_type_type_eq : IsEqualType Γ A A' → IsType Γ A :=
  by
    intro hAA
    apply (And.left (And.right (And.right (And.right boundary_has_type))))
    apply hAA

theorem boundary_has_type_term_eq : IsEqualTerm Γ a a' A → HasType Γ a A :=
  by
    intro haaA
    apply (And.right (And.right (And.right (And.right boundary_has_type))))
    apply haaA
