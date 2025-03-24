import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.WeakSubstitution.WeakSubstitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConv

import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

#check HasType.sigma_elim
-- TODO: first eliminator then computions

theorem this_might_work :
    A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋ =  A⌊↑ₚidₚ⌋⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ :=
  by
    simp [substitution_comp_σρ]
    simp [comp_substitute_weaken]
    simp [weakening_comp]
    simp [comp_weaken]
    apply Eq.symm
    apply conversion_sub_weak

theorem sigma_elim_proj_first :
    ∃a, Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B) → Γ ⊢ a ∶ A :=
  by
    apply Exists.intro
    intro hSi hpSi
    have h := sigma_is_type_inversion hSi
    have C := weakening_type (And.left h) hSi
    have c : (Γ ⬝ A ⬝ B ⊢ v(0)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) :=
        by
          apply HasType.weak
          · apply HasType.var
            apply And.left h
          · apply And.right h
    rw [this_might_work] at c
    have ind := HasType.sigma_elim hpSi C c
    rw [substitution_shift_substitute_zero] at ind
    apply ind

def sigma_elim_π₁ (Si : Γ ⊢ ΣA;B type) (pSi : Γ ⊢ p ∶ ΣA;B) : Γ ⊢ A.indSigma B (A⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) p ∶ A :=
  have h := sigma_is_type_inversion Si
  have C := weakening_type (And.left h) Si
  have c : (Γ ⬝ A ⬝ B ⊢ v(0)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) :=
      by
        rw [←this_might_work]
        apply HasType.weak
        · apply HasType.var
          apply And.left h
        · apply And.right h
  have ind : Γ ⊢ A.indSigma B (A⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) p ∶ A := 
    by
      have h := HasType.sigma_elim pSi C c
      rw [substitution_shift_substitute_zero] at h
      apply h
  ind

theorem sigma_comp_proj_first :
    ∀a b, Γ ⊢ ΣA;B type → (Γ ⊢ a&b ∶ ΣA;B) → Γ ⊢ a ∶ A :=
  by
    intro a b
    intro hSi hpSi
    have h := sigma_is_type_inversion hSi
    have C := weakening_type (And.left h) hSi
    have c : (Γ ⬝ A ⬝ B ⊢ v(0)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) := -- C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉)
        by
          apply HasType.weak
          · apply HasType.var
            apply And.left h
          · apply And.right h
    rw [this_might_work] at c
    sorry
    -- have ind := IsEqualTerm.sigma_comp sorry sorry C c
    -- rw [substitution_shift_substitute_zero] at ind
    -- apply ind

theorem sigma_elim_proj_second :
    ∃b, (Γ ⊢ p ∶ ΣA;B) → Γ ⊢ b ∶ B⌈a⌉₀  := -- how to correctly express a?
  by
    apply Exists.intro
    intro hpSi
    have hSi := boundary_term_type hpSi
    have h := sigma_is_type_inversion hSi
    have C := weakening_type (And.left h) hSi
    have c : (Γ ⬝ A ⬝ B ⊢ v(0)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) := -- C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉)
        by
          apply HasType.weak
          · apply HasType.var
            apply And.left h
          · apply And.right h
    rw [this_might_work] at c
    have ind := HasType.sigma_elim hpSi C c
    rw [substitution_shift_substitute_zero] at ind
    any_goals sorry
    -- apply ind

