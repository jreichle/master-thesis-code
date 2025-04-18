import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.RulesEquality

import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.WeakSubstitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConversion

import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

theorem sigma_elim_proj_first :
    Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B) →  Γ ⊢ A.indSigma B (A⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) p  ∶ A :=
  by
    intro hSi hpSi
    have h := sigma_is_type_inversion hSi
    have C := weakening_type (And.left h) hSi
    have c : (Γ ⬝ A ⬝ B ⊢ v(0)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) :=
        by
          apply HasType.weak
          · apply HasType.var
            apply And.left h
          · apply And.right h
    have ind :=
      by
        apply HasType.sigma_elim
        · apply hpSi
        · apply C
        · replace_by_conclusion c
          · apply congr
            · rfl
            · substitution_step
          · apply c
    simp [] at ind
    apply ind

theorem sigma_comp_proj_first :
    Γ ⊢ ΣA;B type → (Γ ⊢ a ∶ A) → (Γ ⊢ b ∶ B⌈a⌉₀)
    → Γ ⊢ A.indSigma B (A⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) (a&b) ≡ a ∶ A :=
  by
    intro hSi haA hbB
    have hSiInv := sigma_is_type_inversion hSi
    have hA := And.left hSiInv
    have hB := And.right hSiInv
    have hC := weakening_type hA hSi
    have hcC : Γ ⬝ A ⬝ B ⊢ v(0)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ :=
      by
        have h := weakening_term (HasType.var hA) hB
        replace_by_conclusion h
        · apply congr
          · rfl
          · substitution_step
        · apply h
    have hComp := IsEqualTerm.sigma_comp haA hbB hC hcC
    simp [] at hComp
    apply hComp

theorem sigma_elim_proj_second_pre' :
    Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B)
    → Γ ⬝ A ⬝ B ⊢ v(0) ∶
        B⌊⇑ₚ↑ₚidₚ⌋⌊⇑ₚ↑ₚidₚ⌋
        ⌈.indSigma (A⌊↑ₚ↑ₚidₚ⌋) (B⌊⇑ₚ↑ₚ↑ₚidₚ⌋) (A⌊↑ₚ↑ₚ↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) (v(1)&v(0))⌉₀ :=
  by
    intro hSi hpSi
    have hSiInv := sigma_is_type_inversion hSi
    have hA := And.left hSiInv
    have hB := And.right hSiInv
    have h1 := weakening_second_type hB hA
    have h2 := weakening_second_type h1 hB
    have h3 : Γ ⬝ A ⬝ B ⊢
        B⌊⇑ₚ↑ₚidₚ⌋⌊⇑ₚ↑ₚidₚ⌋⌈.indSigma (A⌊↑ₚ↑ₚidₚ⌋) (B⌊⇑ₚ↑ₚ↑ₚidₚ⌋) (A⌊↑ₚ↑ₚ↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) (v(1)&v(0))⌉₀
        ≡ B⌊⇑ₚ↑ₚidₚ⌋⌊⇑ₚ↑ₚidₚ⌋⌈v(1)⌉₀ type :=
      by
        apply functionality_typing_type
        · apply h2
        · rw (config := {occs := .pos [1]}) [←weakening_shift_id]
          rw (config := {occs := .pos [3]}) [←weakening_shift_id]
          rw (config := {occs := .pos [4]}) [←weakening_shift_id]
          apply sigma_comp_proj_first
          · apply IsType.sigma_form
            · apply weakening_type
              · apply weakening_type hA hA
              · apply hB
            · rw (config := {occs := .pos [2]}) [weakening_comp] at h2
              simp only [comp_weaken] at h2
              apply h2
          · apply useWeakwithWeak (i := 0)
            · apply HasType.var hA
            · apply hB
            · rfl
            · rfl
          · apply useVarwithWeak
            · apply hB
            · simp [substitution_comp_σρ]
        · rw (config := {occs := .pos [1]}) [←weakening_shift_id]
          rw (config := {occs := .pos [3]}) [←weakening_shift_id]
          rw (config := {occs := .pos [4]}) [←weakening_shift_id]
          apply sigma_elim_proj_first
          · apply IsType.sigma_form
            · apply weakening_type
              · apply weakening_type hA hA
              · apply hB
            · replace_by_conclusion h2
              · apply congr
                · rfl
                · substitution_step
              · apply h2
          · apply HasType.sigma_intro
            · apply useWeakwithWeak (i := 0) (A := A⌊↑ₚidₚ⌋)
              · apply HasType.var hA
              · apply hB
              · rfl
              · rfl
            · apply useVarwithWeak
              · apply hB
              · simp [substitution_comp_σρ]
            · rw (config := {occs := .pos [2]}) [weakening_comp] at h2
              simp only [comp_weaken] at h2
              apply h2
        · apply useWeakwithWeak (i := 0)
          · apply HasType.var
            apply hA
          · apply hB
          · rfl
          · rfl
    apply HasType.ty_conv
    case A => apply B⌊⇑ₚ↑ₚidₚ⌋⌊⇑ₚ↑ₚidₚ⌋⌈v(1)⌉₀
    · simp []
      substitution_to_composition
      simp []
      apply HasType.var hB
    · apply IsEqualType.type_symm
      apply h3

theorem sigma_elim_proj_second_pre :
    Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B)
    → Γ ⬝ A ⬝ B ⊢ v(0) ∶
        B⌊⇑ₚ↑ₚidₚ⌋
          ⌈A⌊↑ₚidₚ⌋.indSigma (B⌊1ₙ⇑ₚ(↑ₚidₚ)⌋) (A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) v(0)⌉₀⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉
 :=
  by
    intro hSi hpSi
    have h := sigma_elim_proj_second_pre' hSi hpSi
    replace_by_conclusion h
    · apply congr
      · rfl
      · substitution_step
        substitution_step
        any_goals substitution_step
        · rw [←substitution_id (t := B)]
          substitution_to_composition
          substitution_var_sub
          any_goals substitution_step
        · rw [←substitution_id (t := A)]
          substitution_to_composition
          substitution_var_sub
          any_goals substitution_step
    · apply h

theorem sigma_elim_proj_second {n : Nat} {Γ : Ctx n} {A p : Tm n} {B : Tm (n + 1)} :
    Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B)
    → Γ ⊢ A.indSigma B
          (B⌊⇑ₚ↑ₚidₚ⌋⌈.indSigma (A⌊↑ₚidₚ⌋) (B⌊⇑ₚ↑ₚidₚ⌋) (A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) (v(0))⌉₀)
          v(0) p
        ∶ B⌈A.indSigma B (A⌊↑ₚidₚ⌋) (v(1)) p⌉₀ :=
  by
    intro hSi hpSi
    have hSiInv := sigma_is_type_inversion hSi
    have hA := And.left hSiInv
    have hB := And.right hSiInv
    have hCpre : Γ ⬝ (ΣA;B) ⬝ A⌊↑ₚidₚ⌋ ⊢ B⌊⇑ₚ↑ₚidₚ⌋ type := weakening_second_type hB hSi
    have hC :=
      by
        apply substitution_type
        · apply hCpre
        · apply sigma_elim_proj_first
          · apply weakening_type hSi hSi
          · apply HasType.var hSi
    have hcCpre := sigma_elim_proj_second_pre hSi hpSi
    have hcC : Γ ⬝ A ⬝ B ⊢ v(0) ∶
                  B⌊⇑ₚ↑ₚidₚ⌋⌈A⌊↑ₚidₚ⌋.indSigma
                    (B⌊1ₙ⇑ₚ(↑ₚidₚ)⌋) (A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) v(0)⌉₀⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ :=
      by
        apply sigma_elim_proj_second_pre
        · apply hSi
        · apply hpSi
    have hElim := HasType.sigma_elim hpSi hC hcC
    replace_by_conclusion hElim
    · apply congr
      · rfl
      · substitution_step
        substitution_step
        · rw [←substitution_id (t := B)]
          substitution_to_composition
          substitution_var_sub
          any_goals substitution_step
        · rw [←substitution_id (t := A)]
          substitution_to_composition
          substitution_var_sub
          any_goals substitution_step
    · apply hElim

theorem sigma_comp_proj_second {n : Nat} {Γ : Ctx n} {A a b : Tm n} {B : Tm (n + 1)} :
    Γ ⊢ ΣA;B type → (Γ ⊢ a ∶ A) → (Γ ⊢ b ∶ B⌈a⌉₀)
    → Γ ⊢ A.indSigma B
            (B⌊⇑ₚ↑ₚidₚ⌋⌈.indSigma (A⌊↑ₚidₚ⌋) (B⌊⇑ₚ↑ₚidₚ⌋) (A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) (v(0))⌉₀)
            v(0) (a&b)
          ≡ b
          ∶ B⌈A.indSigma B (A⌊↑ₚidₚ⌋) (v(1)) (a&b)⌉₀ :=
  by
    intro hSi haA hbB
    have hSiInv := sigma_is_type_inversion hSi
    have hA := And.left hSiInv
    have hB := And.right hSiInv
    have hpSi := HasType.sigma_intro haA hbB hB
    have hCpre : Γ ⬝ (ΣA;B) ⬝ A⌊↑ₚidₚ⌋ ⊢ B⌊⇑ₚ↑ₚidₚ⌋ type := weakening_second_type hB hSi
    have hC :=
      by
        apply substitution_type
        · apply hCpre
        · apply sigma_elim_proj_first
          · apply weakening_type hSi hSi
          · apply HasType.var hSi
    have hcCpre := sigma_elim_proj_second_pre hSi hpSi
    have hcC : Γ ⬝ A ⬝ B ⊢ v(0) ∶
                  B⌊⇑ₚ↑ₚidₚ⌋⌈A⌊↑ₚidₚ⌋.indSigma
                    (B⌊1ₙ⇑ₚ(↑ₚidₚ)⌋) (A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) v(0)⌉₀⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ :=
      by
        apply sigma_elim_proj_second_pre
        · apply hSi
        · apply hpSi
    have hComp := IsEqualTerm.sigma_comp haA hbB hC hcC
    replace_by_conclusion hComp
    · apply congr
      · rfl
      · substitution_step
        substitution_step
        · rw [←substitution_id (t := B)]
          substitution_to_composition
          substitution_var_sub
          any_goals substitution_step
        · rw [←substitution_id (t := A)]
          substitution_to_composition
          substitution_var_sub
          any_goals substitution_step
    · apply hComp

def π₁ : Tm n :=
  λ𝒰; λ(Πv(0);𝒰); λ(Σv(1);(Πv(2);𝒰)); (.indSigma v(2) (Πv(3);𝒰) (v(3)) (v(1)) (v(0)))

def π₂ : Tm n :=
  λ𝒰; λ(Πv(0);𝒰); λ(Σv(1);(Πv(2);𝒰)); (.indSigma v(2) (Πv(3);𝒰)
    ((Πv(3);𝒰)⌈π₁◃v(3)◃(Πv(3);𝒰)◃v(0)⌉₀)
    -- (B⌊⇑ₚ↑ₚidₚ⌋⌈.indSigma (A⌊↑ₚidₚ⌋) (B⌊⇑ₚ↑ₚidₚ⌋) (A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) (v(0))⌉₀)
    (v(0)) (v(0)))

theorem proj_one_type :
    (ε ⊢ π₁ ∶ Π𝒰; Π(Πv(0);𝒰); Π(Σv(1);(Πv(2);𝒰)); v(2)) :=
  by
    rw [π₁]
    apply HasType.pi_intro
    apply HasType.pi_intro
    apply HasType.pi_intro
    have hU : ε ⬝ 𝒰 ⊢ v(0) type :=
      by
        apply IsType.univ_elim
        apply useVarwithWeak
        · aesop
        · rfl
    have hPi : ε ⬝ 𝒰 ⊢ Πv(0);𝒰 type :=
      by
        apply IsType.pi_form
        · apply hU
        · apply IsType.univ_form
          aesop
    have hvA : (ε ⬝ 𝒰 ⬝ Πv(0);𝒰) ⊢ v(1) ∶ 𝒰 :=
      by
        apply useWeakwithWeak (i := 0) (A := 𝒰)
        · apply HasType.var
          aesop
        · apply hPi
        · rfl
        · rfl
    have hSi : (ε ⬝ 𝒰 ⬝ Πv(0);𝒰) ⊢ Σv(1);Πv(2);𝒰 type :=
      by
        apply IsType.sigma_form
        · apply IsType.univ_elim
          apply useWeakwithWeak
          · apply HasType.var
            apply IsType.univ_form
            apply IsCtx.empty
          · apply hPi
          · rfl
          · rfl
        · apply IsType.pi_form
          · apply IsType.univ_elim
            apply useWeakwithWeak (i := 1) (A := 𝒰)
            · apply hvA
            · apply IsType.univ_elim
              apply hvA
            · rfl
            · rfl
          · apply IsType.univ_form
            apply IsCtx.extend
            · apply IsCtx.extend
              · apply boundary_ctx_term hvA
              · apply IsType.univ_elim hvA
            · apply IsType.univ_elim
              apply useWeakwithWeak (i := 1) (A := 𝒰)
              · apply hvA
              · apply IsType.univ_elim hvA
              · rfl
              · rfl
    have hpSi : ((ε ⬝ 𝒰 ⬝ Πv(0);𝒰) ⬝ Σv(1);Πv(2);𝒰) ⊢ v(2) type :=
      by
        apply useWeakTypewithWeak (A := v(1))
        · apply IsType.univ_elim
          apply hvA
        · apply hSi
        · rfl
    apply HasType.sigma_elim
    · apply useVarwithWeak
      · apply hSi
      · simp []
    · apply useWeakTypewithWeak (A := v(2))
      · apply hpSi
      · apply useWeakTypewithWeak
        · apply hSi
        · apply hSi
        · rfl
      · rfl
    · simp []
      apply useWeakTermwithWeak (a := v(0)) (A := v(3))
      · apply HasType.var
        apply hpSi
      · apply IsType.pi_form
        · apply useWeakTypewithWeak (A := v(2))
          · apply hpSi
          · apply hpSi
          · rfl
        · apply IsType.univ_form
          apply IsCtx.extend
          · apply IsCtx.extend
            · apply boundary_ctx_type hpSi
            · apply hpSi
          · apply useWeakTypewithWeak (A := v(2))
            · apply hpSi
            · apply hpSi
            · rfl
      · rfl
      · rfl
