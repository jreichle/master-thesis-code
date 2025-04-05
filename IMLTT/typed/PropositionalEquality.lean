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

theorem pi_same_type_diff_val :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (Γ ⊢ Π(P⌈a⌉₀);(P⌈a'⌉₀⌊↑ₚidₚ⌋) type) :=
  by
    intro hP haA haA'
    apply IsType.pi_form
    · apply substitution_type
      · apply haA
      · apply hP
    · apply weakening_type
      · apply substitution_type
        · apply haA'
        · apply hP
      · apply substitution_type
        · apply haA
        · apply hP

theorem how_to :
    P⌈(ₛ↑ₚ↑ₚidₚ), v(0)⌉ = P⌈(ₛ↑ₚidₚ), v(0)⌉⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    rw [substitution_comp_ρσ]
    simp [comp_weaken_substitute]
    simp [comp_weaken]
    simp [weaken]
    simp [weaken_var]
    rfl

theorem pi_same_type_diff_var_context {n : Nat} {Γ : Ctx n} {A : Tm n} {P : Tm (n + 1)}:
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ), v(0)⌉⌊↑ₚidₚ⌋) type) :=
  by
    intro hP
    have hA := ctx_extr (boundary_ctx_type hP)
    apply IsType.pi_form
    · apply weakening_type
      · apply hP
      · apply weakening_type hA hA
    · apply weakening_type
      · rw [how_to]
        apply weakening_second_type
        · rw [substitution_id_shift_var]
          apply hP
        · apply hA
      · apply weakening_type
        · apply hP
        · apply weakening_type hA hA

theorem pi_same_type_diff_var_context_iden_weak :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) 
              ⊢ (Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ), v(0)⌉⌊↑ₚidₚ⌋))⌊↑ₚidₚ⌋ type :=
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

theorem this_works_aaaaah :
    P⌈↑ₛ((ₛ↑ₚ↑ₚidₚ), (v(0)⌊idₚ⌋))⌉⌈1ₙ⇑ₛ((ₛidₚ), v(0))⌉
    = P⌊↑ₚidₚ⌋ :=
  by
    rw [←substitution_conv_shift_id]
    rw [weakening_id]
    rw [how_to]
    rw [substitution_id_shift_var]
    simp [lift_subst_n]
    simp [weakening_comp]
    simp [substitution_comp_σρ]
    simp [comp_weaken]
    simp [comp_substitute_weaken]
    rw [←substitution_conv_shift_id]
    simp [comp_weaken]
    rw [substitution_id_shift_var]

theorem inhabitant_pi_same_type_diff_val :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⊢ λP;v(0) ∶ (Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ), v(0)⌉⌊↑ₚidₚ⌋))⌈(ₛidₚ), v(0)⌉) :=
  by
    intro hP
    have hA := ctx_extr (boundary_ctx_type hP)
    simp [substitute]
    rw [substitution_comp_ρσ]
    rw [substitution_comp_σρ]
    simp [comp_weaken_substitute]
    simp [comp_substitute_weaken]
    simp [substitution_id]
    apply HasType.pi_intro
    rw [this_works_aaaaah]
    apply HasType.var
    apply hP

theorem rewrite_keep_sub :
    B⌈(ₛidₚ), v(0)⌉ =
    B⌊↑ₚidₚ⌋⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉ :=
  by
    simp [substitution_comp_σρ]
    simp [comp_substitute_weaken]

theorem rewrite_elim :
    (ΠP⌊↑ₚidₚ⌋;P⌈(ₛ↑ₚ↑ₚidₚ), v(0)⌉⌊↑ₚidₚ⌋)⌊↑ₚidₚ⌋⌈(ₛidₚ), a, a', p⌉
    = (ΠP⌈(ₛidₚ), a⌉;P⌈(ₛidₚ), a'⌉⌊↑ₚidₚ⌋) :=
  by
    simp [weaken]
    simp [substitute]
    rw [substitution_comp_ρσ]
    rw [substitution_comp_σρ]
    simp [comp_weaken_substitute]
    simp [comp_substitute_weaken]
    simp [weakening_id]
    simp [lift_weak_n]
    apply And.intro
    · rw [substitution_comp_σρ]
      simp [comp_substitute_weaken]
    · rw [substitution_comp_σρ]
      simp [lift_subst_n]
      simp [comp_substitute_weaken]
      simp [substitution_comp]
      simp [comp_substitute_substitute]
      simp [comp_substitute_weaken]
      simp [substitute]
      simp [substitute_var]
      rw [←substitution_conv_shift_id]
      aesop

theorem leibniz_principle {n : Nat} {Γ : Ctx n} {A p a a' h : Tm n} {B : Tm (n + 3)} {h' P : Tm (n + 1)} :
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
    rw [rewrite_keep_sub] at hbB
    have hElimId := HasType.iden_elim hB hbB (And.left (And.right hIdInv)) (And.right (And.right hIdInv)) hpId
    rw [rewrite_elim] at hElimId
    have hElimPi := HasType.pi_elim hElimId hhP
    rw [substitution_shift_substitute_zero] at hElimPi
    apply hElimPi

theorem helper_prop_eq_trans_id_subst_left :
    (a₁ ≃[A] a₂) =
    (v(0) ≃[A⌊↑ₚidₚ⌋] a₂⌊↑ₚidₚ⌋)⌈(ₛidₚ), a₁⌉ :=
  by
    rw [substitute]
    simp
    repeat' apply And.intro
    · rw [substitution_conv_zero]
      rw [substitution_shift_substitute_zero]
    · simp [substitute]
      simp [substitute_var]
      rfl
    · rw [substitution_conv_zero]
      rw [substitution_shift_substitute_zero]

theorem helper_prop_eq_trans_id_subst_right :
    (a₁ ≃[A] a₂) =
    (a₁⌊↑ₚidₚ⌋ ≃[A⌊↑ₚidₚ⌋] v(0))⌈(ₛidₚ), a₂⌉ :=
  by
    rw [substitute]
    simp
    repeat' apply And.intro
    · rw [substitution_conv_zero]
      rw [substitution_shift_substitute_zero]
    · rw [substitution_conv_zero]
      rw [substitution_shift_substitute_zero]
    · simp [substitute]
      simp [substitute_var]
      rfl

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
    rw [rewrite_keep_sub] at hbB
    have hElimId := HasType.iden_elim hB hbB (And.left (And.right hIdInv)) (And.right (And.right hIdInv)) hpId
    rw [rewrite_elim] at hElimId
    rw [helper_prop_eq_trans_id_subst_left] at hreflId
    have hElimPi := HasType.pi_elim hElimId hreflId
    rw [substitution_shift_substitute_zero] at hElimPi
    rw [←helper_prop_eq_trans_id_subst_left] at hElimPi
    apply hElimPi

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
    rw [rewrite_keep_sub] at hbB
    have hElimId := HasType.iden_elim hB hbB (And.left (And.right hIdInv')) (And.right (And.right hIdInv')) hpId'
    rw [rewrite_elim] at hElimId
    rw [←helper_prop_eq_trans_id_subst_right] at hElimId
    have hElimPi := HasType.pi_elim hElimId hpId
    rw [substitution_shift_substitute_zero] at hElimPi
    rw [←helper_prop_eq_trans_id_subst_right] at hElimPi
    apply hElimPi
