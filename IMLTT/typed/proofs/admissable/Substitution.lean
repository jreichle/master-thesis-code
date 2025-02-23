import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.proofs.Substitution

import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.SubstitutionGeneral

import aesop

/- # Substitution Property -/

theorem substitution_ctx : 
    (Γ ⊢ b ∶ B) → Γ ⬝ B ⬝ A ctx → Γ ⬝ A⌈b⌉₀ ctx :=
  by
    intro hbB hiCBA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    rw [extend_expand_context_n_substitution]
    apply And.left substitution
    · apply hiCBA
    · apply hbB
    omega

theorem substitution_type : (Γ ⊢ b ∶ B) → Γ ⬝ B ⊢ A type → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro hbB hA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right substitution)
    · apply hA
    · apply hbB

theorem substitution_term : 
    (Γ ⊢ b ∶ B) → (Γ ⬝ B ⊢ a ∶ A) → Γ ⊢ a⌈b⌉₀ ∶ A⌈b⌉₀ :=
  by
    intro hbB haA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right (And.right substitution))
    · apply haA
    · apply hbB

theorem substitution_type_eq :
    (Γ ⊢ b ∶ B) → Γ ⬝ B ⊢ A ≡ A' type → Γ ⊢ A⌈b⌉₀ ≡ A'⌈b⌉₀ type :=
  by
    intro hbB hAA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right (And.right (And.right substitution)))
    · apply hAA
    · apply hbB


theorem substitution_term_eq : 
    (Γ ⊢ b ∶ B) → (Γ ⬝ B ⊢ a ≡ a' ∶ A) → Γ ⊢ a⌈b⌉₀ ≡ a'⌈b⌉₀ ∶ A⌈b⌉₀ :=
  by
    intro hbB haaA
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.right (And.right (And.right (And.right substitution)))
    · apply haaA
    · apply hbB


-- helper

theorem substitution_inv_type :
    B' = B⌈a⌉₀ → Γ ⊢ B' type → (Γ ⊢ a ∶ A) → Γ ⬝ A ⊢ B type :=
  by
    intro hBeqB' hBs haA
    match hBs with
    | .unit_form hiC =>
      sorry
    | _ => sorry

theorem substitution_inv_type_eq :  -- won't work, add counterexample
    B' = B⌈a⌉₀ → C' = C⌈a⌉₀ → Γ ⊢ B' ≡ C' type → (Γ ⊢ a ∶ A) → Γ ⬝ A ⊢ B ≡ C type :=
  by
    sorry

theorem tm_not_type : ¬(∀ {n : Nat} {Γ : Ctx n} {a : Tm n}, Γ ⊢ a type) :=
  by
    intro ha
    have h := ha (Γ := ε ⬝ 𝟙) (a := v(0))
    cases h
    case univ_elim h1 =>
      cases h1
      sorry

theorem substitution_inv_type' {m : Nat} {Γ : Ctx m} {a A : Tm m} {B : Tm (m + 1)} :
    Γ ⊢ A type → Γ ⊢ B⌈a⌉₀ type → (Γ ⊢ a ∶ A) → Γ ⬝ A ⊢ B type :=
  by
    intro hA hB haA
    apply IsType.recOn
      (motive_1 := fun Γ _hiC => True)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ (eqM :m = n),
        eqM ▸ Γ = Γ' → eqM ▸ A' = B⌈a⌉₀
        → Γ ⬝ A ⊢ B type
      )
      (motive_3 := fun Γ x X _haA => True)
      (motive_4 := fun Γ A A' _hAA => True)
      (motive_5 := fun Γ a a' A _haaA => True)
      hB
    case unit_form =>
      intro n Γ' hiC _ heqM heqΓ heqB
      cases heqM
      cases heqΓ
      rw [←heqB] at hB
      have hw := weakening_type hB hA
      rw [weaken] at hw
      -- problem: see substitution_unit_sub
      -- so: case B = v(0) and case B ≠ v(0)
      cases B with
      | unit => apply hw
      | var x =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [substitute_zero] at heqB
            simp [substitute] at heqB
            simp [substitute_var] at heqB
            simp_all
            -- find contradiction in assumptions
            -- have h := tm_not_type hB
            sorry
          | succ i' =>
            simp [substitute_zero] at heqB
            simp [substitute] at heqB
            simp [substitute_var] at heqB
            simp [weakening_id] at heqB
      | _ => sorry
    case empty_form =>
      sorry
    case pi_form =>

      intro n Γ' A' B' hA hB ihA ihB heqM heqΓ heqT
      cases heqM
      cases heqΓ
      sorry
    case sigma_form =>
      sorry
    case iden_form =>
      sorry
    case univ_form =>
      sorry
    case univ_elim =>
      sorry
    any_goals sorry
