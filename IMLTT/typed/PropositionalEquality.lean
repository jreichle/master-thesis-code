import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.WeakSubstitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConversion

import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

-- FIXME: redo but use only simplified types, not abominations

theorem pi_same_type_diff_val :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (Γ ⊢ Π(P⌈a⌉₀);(P⌈a'⌉₀⌊↑ₚidₚ⌋) type) :=
  by
    intro hP haA haA'
    apply IsType.pi_form
    · apply substitution_type
      · apply hP
      · apply haA
    · apply weakening_type
      · apply substitution_type
        · apply hP
        · apply haA'
      · apply substitution_type
        · apply hP
        · apply haA

theorem pi_same_type_diff_var_context {n : Nat} {Γ : Ctx n} {A : Tm n} {P : Tm (n + 1)}:
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(0)⌉⌊↑ₚidₚ⌋) type) :=
  by
    intro hP
    have hA := ctx_extr (boundary_ctx_type hP)
    apply IsType.pi_form
    · apply weakening_type
      · apply hP
      · apply weakening_type hA hA
    · apply weakening_type
      · replace_by_conclusion weakening_second_type
        rotate_left
        · apply weakening_second_type hP hA
        · apply congr
          · rfl
          · rw [←substitution_id (t := P)]
            substitution_to_composition
            substitution_var_sub
            any_goals substitution_step
      · apply weakening_type
        · apply hP
        · apply weakening_type hA hA

theorem pi_same_type_diff_var_context_iden_weak :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) 
              ⊢ (Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(0)⌉⌊↑ₚidₚ⌋))⌊↑ₚidₚ⌋ type :=
  by
    intro hP
    have hA := ctx_extr (boundary_ctx_type hP)
    have hT := pi_same_type_diff_var_context hP
    apply weakening_type
    · apply hT
    · apply IsType.iden_form
      · rw (config := {occs := .pos [1]}) [←weakening_shift_id]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        apply weakening_type
        · apply weakening_type
          · apply hA
          · apply hA
        · rw [weakening_id]
          apply weakening_type
          · apply hA
          · apply hA
      · rw [weakening_shift_vone]
        rw (config := {occs := .pos [3]}) [←weakening_shift_id]
        apply HasType.weak
        · apply HasType.var hA
        · apply weakening_type
          · apply hA
          · apply hA
      · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        apply HasType.var
        apply weakening_type
        · apply hA
        · apply hA

theorem inhabitant_pi_same_type_diff_val :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⊢ λP;v(0) ∶ (Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(0)⌉⌊↑ₚidₚ⌋))⌈(ₛidₚ)⋄ v(0)⌉) :=
  by
    intro hP
    have hA := ctx_extr (boundary_ctx_type hP)
    have h := HasType.pi_intro (HasType.var hP)
    replace_by_conclusion_resolve h

theorem leibniz_principle {n : Nat} {Γ : Ctx n} {A p a a' h : Tm n} {P : Tm (n + 1)} :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⊢ p ∶ a ≃[A] a')
    → (Γ ⊢ h ∶ P⌈a⌉₀)
    → ∃h', (Γ ⊢ h' ∶ P⌈a'⌉₀)
    :=
  by
    intro hP hpId hhP
    have hA := ctx_extr (boundary_ctx_type hP)
    have hId := boundary_term_type hpId
    have hIdInv := iden_is_type_inversion hId
    apply Exists.intro
    have hB := pi_same_type_diff_var_context_iden_weak hP
    have hbB := inhabitant_pi_same_type_diff_val hP
    have hElimId := HasType.iden_elim hB
                    (by
                      replace_by_conclusion hbB
                      · apply congr
                        · rfl
                        · substitution_step
                      · apply hbB)
                    (And.left (And.right hIdInv)) (And.right (And.right hIdInv)) hpId
    have hElimPi :=
      by
        apply HasType.pi_elim
        rotate_left
        · apply hhP
        rotate_right
        · replace_by_conclusion hElimId
          · apply congr
            apply congr
            · rfl
            · substitution_step_meta
            · substitution_step
              substitution_step
          · apply hElimId
    · replace_by_conclusion hElimPi
      · apply congr
        apply congr
        · rfl
        · substitution_step_meta
        · substitution_step
          substitution_step
      · apply hElimPi

theorem propositional_equality_symm :
    (Γ ⊢ p ∶ a ≃[A] a')
    → ∃p', (Γ ⊢ p' ∶ a' ≃[A] a) :=
  by
    intro hpId
    have hId := boundary_term_type hpId
    have hIdInv := iden_is_type_inversion hId
    have hA := And.left hIdInv
    apply Exists.intro
    have hP : Γ ⬝ A ⊢ v(0) ≃[A⌊↑ₚidₚ⌋] a⌊↑ₚidₚ⌋ type :=
      by
        apply IsType.iden_form
        · apply weakening_type hA hA
        · apply HasType.var hA
        · apply weakening_term (And.left (And.right hIdInv)) hA
    have hreflId : Γ ⊢ .refl A a ∶ (a ≃[A] a) :=
      by
        apply HasType.iden_intro
        · apply hA
        · apply And.left (And.right hIdInv)
    have hB := pi_same_type_diff_var_context_iden_weak hP
    have hbB := inhabitant_pi_same_type_diff_val hP
    have hElimId := HasType.iden_elim hB
                    (by
                      replace_by_conclusion hbB
                      · apply congr
                        · rfl
                        · substitution_step
                      · apply hbB)
                    (And.left (And.right hIdInv)) (And.right (And.right hIdInv)) hpId
    have hElimPi :=
      by
        apply HasType.pi_elim hElimId -- hreflId
        · replace_by_conclusion hreflId
          · apply congr
            · rfl
            · substitution_step
          · apply hreflId
    · replace_by_conclusion hElimPi
      · apply congr
        apply congr
        · rfl
        · substitution_step_meta
        · substitution_step
          substitution_step
          substitution_step
      · apply hElimPi

theorem propositional_equality_trans :
    (Γ ⊢ p₁ ∶ a₁ ≃[A] a₂)
    → (Γ ⊢ p₂ ∶ a₂ ≃[A] a₃)
    → ∃p, (Γ ⊢ p ∶ a₁ ≃[A] a₃) :=
  by
    intro hpId hpId'
    have hId := boundary_term_type hpId
    have hIdInv := iden_is_type_inversion hId
    have hId' := boundary_term_type hpId'
    have hIdInv' := iden_is_type_inversion hId'
    have hA := And.left hIdInv
    apply Exists.intro
    have hP : Γ ⬝ A ⊢ a₁⌊↑ₚidₚ⌋ ≃[A⌊↑ₚidₚ⌋] v(0) type :=
      by
        apply IsType.iden_form
        · apply weakening_type hA hA
        · apply weakening_term (And.left (And.right hIdInv)) hA
        · apply HasType.var hA
    have hB := pi_same_type_diff_var_context_iden_weak hP
    have hbB := inhabitant_pi_same_type_diff_val hP
    have hElimId := HasType.iden_elim hB
                    (by
                      replace_by_conclusion hbB
                      · apply congr
                        · rfl
                        · substitution_step
                      · apply hbB)
                    (And.left (And.right hIdInv')) (And.right (And.right hIdInv')) hpId'
    have hElimPi :=
      by
        apply HasType.pi_elim hElimId
        · replace_by_conclusion hpId
          · apply congr
            · rfl
            · substitution_step
          · apply hpId
    · replace_by_conclusion hElimPi
      · apply congr
        apply congr
        · rfl
        · substitution_step_meta
        · substitution_step
          substitution_step
          substitution_step
      · apply hElimPi
