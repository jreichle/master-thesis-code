import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.weakening.Helpers
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem weakening_type_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type →
      (∀ (l : Nat) {leq : l ≤ x} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from x l⌋ type) →
        ∀ (l : Nat) {leq : l ≤ x + 1} {B : Tm l},
          get_sub_context (Γ ⬝ A) l leq ⊢ B type →
            insert_into_ctx leq (Γ ⬝ A) B ⊢ v(0)⌊weaken_from (x + 1) l⌋ ∶ A⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ :=
  by
    intro x Γ A hA ihA l hleq B hB
    cases hleq
    case refl =>
      simp [weaken_from]
      simp [weakening_comp]
      simp [comp_weaken]
      simp [insert_into_ctx]
      rw [←weakening_shift_id]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      simp [weakening_id]
      apply HasType.weak
      · apply HasType.var hA
      · rw [head_get_sub_context] at hB
        · apply hB
        · rfl
    case step h =>
      rw [←extend_insert_into_context (leq := h)]
      · simp [weakening_comp]
        simp [weaken_from]
        split
        case isTrue hT =>
          simp [comp_weaken]
          rw [←weakening_shift_id]
          simp [←weakening_comp]
          simp [weakening_id]
          simp [weaken]
          simp [weaken_var]
          apply HasType.var
          apply ihA
          rw [extend_get_sub_context] at hB
          apply hB
        case isFalse hF =>
          apply False.elim
          simp [h] at hF
          apply helper_weak_1 h hF

theorem weakening_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A) →
      Γ ⊢ B type →
        (∀ (l : Nat) {leq : l ≤ x} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ v(i)⌊weaken_from x l⌋ ∶ A⌊weaken_from x l⌋) →
          (∀ (l : Nat) {leq : l ≤ x} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ B⌊weaken_from x l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ x + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ B) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ B) B_1 ⊢ v(i)⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ ∶ A⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ :=
  by
    intro n x Γ A B hvA hB ihvA ihB l hleq S hS
    · cases hleq
      case refl =>
        simp [insert_into_ctx]
        simp [weaken_from]
        apply HasType.weak
        · rw [←weakening_conv_var]
          rw [head_get_sub_context (eq := by rfl)] at hS
          rw [head_insert_into_context]
          · cases n with
            | zero =>
              simp [weaken_from]
              rw [←head_insert_into_context]
              apply HasType.weak
              · apply hvA
              · apply hB
            | succ n' =>
              rw [←head_insert_into_context]
              apply HasType.weak
              · apply hvA
              · apply hB
        · rw [head_get_sub_context] at hS
          · apply hS
          · rfl
      case step h =>
        rw [shift_weaken_from]
        · rw [shift_weaken_from]
          · rw [←extend_insert_into_context]
            apply HasType.weak
            · simp [←weakening_conv_var]
              apply ihvA
              rw [extend_get_sub_context] at hS
              · apply hS
            · apply ihB
              rw [extend_get_sub_context] at hS
              apply hS
            · exact h
          · exact h
        · exact h

theorem weakening_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ ⋆⌊weaken_from n l⌋ ∶ 𝟙⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply HasType.unit_intro
    apply ihiC
    apply hB

theorem weakening_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ∶ B) →
      (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
          get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
            insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ b⌊weaken_from (n + 1) l⌋ ∶ B⌊weaken_from (n + 1) l⌋) →
        ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
          get_sub_context Γ l leq ⊢ B_1 type →
            insert_into_ctx leq Γ B_1 ⊢ (λA; b)⌊weaken_from n l⌋ ∶ (ΠA;B)⌊weaken_from n l⌋ :=
  by
    intro n Γ A b B hbB ihbB l hleq S hS
    apply HasType.pi_intro
    rw [extend_insert_into_context]
    simp [lift_weak_n]
    rw [lift_weaken_from]
    apply ihbB
    simp [get_sub_context]
    split
    · exact hS
    · omega
    omega

theorem weakening_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A) →
      (Γ ⊢ b ∶ B⌈a⌉₀) →
        Γ ⬝ A ⊢ B type →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                get_sub_context Γ l leq ⊢ B_1 type →
                  insert_into_ctx leq Γ B_1 ⊢ b⌊weaken_from n l⌋ ∶ B⌈a⌉₀⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
                  get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                    insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ type) →
                ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                  get_sub_context Γ l leq ⊢ B_1 type →
                    insert_into_ctx leq Γ B_1 ⊢ a&b⌊weaken_from n l⌋ ∶ (ΣA;B)⌊weaken_from n l⌋ :=
  by
    intro n Γ a A b B haA hbB hB ihaA ihbB ihB l hleq S hS
    apply HasType.sigma_intro
    · apply ihaA
      apply hS
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      · simp [weaken_from]
        split
        case a.isTrue h =>
          rw [←weak_sub_zero]
          apply ihbB
          apply hS
        case a.isFalse h =>
          omega
      · exact hleq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      apply ihB
      rw [extend_get_sub_context]
      apply hS
      any_goals omega

theorem weakening_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
      ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
        get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝓏⌊weaken_from n l⌋ ∶ 𝒩⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply HasType.nat_zero_intro
    apply ihiC
    apply hB

theorem weakening_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩) →
    (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
        get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ x⌊weaken_from n l⌋ ∶ 𝒩⌊weaken_from n l⌋) →
      ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
        get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝓈(x)⌊weaken_from n l⌋ ∶ 𝒩⌊weaken_from n l⌋ :=
  by
    intro n Γ i hiNat ihiNat l hleq S hS
    apply HasType.nat_succ_intro
    apply ihiNat
    apply hS

theorem weakening_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    Γ ⊢ A type →
      (Γ ⊢ a ∶ A) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A.refl a⌊weaken_from n l⌋ ∶ (a ≃[A] a)⌊weaken_from n l⌋ :=
  by
    intro n Γ A a hA haA ihA ihaA l hleq B hB
    apply HasType.iden_intro
    · apply ihA
      apply hB
    · apply ihaA
      apply hB

theorem weakening_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝟙⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply HasType.univ_unit
    apply ihiC
    apply hB

theorem weakening_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝟘⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply HasType.univ_empty
    apply ihiC
    apply hB

theorem weakening_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ∶ 𝒰) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ∶ 𝒰⌊weaken_from (n + 1) l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (ΠA;B)⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ A B hAU hBU ihAU ihBU l hleq S hS
    simp [weaken] at *
    simp [lift_weak_n]
    apply HasType.univ_pi
    · apply ihAU
      · apply hS
    · rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihBU
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega

theorem weakening_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ∶ 𝒰) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ∶ 𝒰⌊weaken_from (n + 1) l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (ΣA;B)⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ A B hAU hBU ihAU ihBU l hleq S hS
    simp [weaken] at *
    simp [lift_weak_n]
    apply HasType.univ_sigma
    · apply ihAU
      · apply hS
    · rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihBU
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega

theorem weakening_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝒩⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply HasType.univ_nat
    apply ihiC
    apply hB

theorem weakening_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
                ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ (a ≃[A] a')⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA' l hleq B hB
    simp [weaken]
    apply HasType.univ_iden
    · apply ihAU
      · apply hB
    · apply ihaA
      · apply hB
    · apply ihaA'
      · apply hB

theorem weakening_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type →
      (Γ ⊢ a ∶ A⌈⋆⌉₀) →
        (Γ ⊢ b ∶ 𝟙) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B : Tm l},
              get_sub_context (Γ ⬝ 𝟙) l leq ⊢ B type → insert_into_ctx leq (Γ ⬝ 𝟙) B ⊢ A⌊weaken_from (n + 1) l⌋ type) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type →
                  insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌈⋆⌉₀⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ b⌊weaken_from n l⌋ ∶ 𝟙⌊weaken_from n l⌋) →
                ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ A.indUnit b a⌊weaken_from n l⌋ ∶ A⌈b⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A a b hA haA hb1 ihA ihaA ihb1 l hleq B hB
    rw [weak_sub_zero]
    apply HasType.unit_elim
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_unit]
      rw [extend_insert_into_context]
      apply ihA
      · rw [extend_get_sub_context]
        exact hB
      · exact hleq
    · simp [lift_weak_n]
      simp [lift_single_subst_tt]
      apply ihaA
      apply hB
    · apply ihb1
      apply hB

theorem weakening_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type →
      (Γ ⊢ b ∶ 𝟘) →
        (∀ (l : Nat) {leq : l ≤ n + 1} {B : Tm l},
            get_sub_context (Γ ⬝ 𝟘) l leq ⊢ B type → insert_into_ctx leq (Γ ⬝ 𝟘) B ⊢ A⌊weaken_from (n + 1) l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ b⌊weaken_from n l⌋ ∶ 𝟘⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A.indEmpty b⌊weaken_from n l⌋ ∶ A⌈b⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A b hA hb0 ihA ihb0 l hleq S hS
    rw [weak_sub_zero]
    apply HasType.empty_elim
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_empty]
      rw [extend_insert_into_context]
      apply ihA
      · rw [extend_get_sub_context]
        exact hS
      · exact hleq
    · apply ihb0
      apply hS

theorem weakening_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B) →
      (Γ ⊢ a ∶ A) →
        (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
            get_sub_context Γ l leq ⊢ B_1 type →
              insert_into_ctx leq Γ B_1 ⊢ f⌊weaken_from n l⌋ ∶ (ΠA;B)⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ f◃a⌊weaken_from n l⌋ ∶ B⌈a⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ f A B a hfPi haA ihfPi ihaA l hleq S hS
    rw [weak_sub_zero]
    · apply HasType.pi_elim
      · apply ihfPi
        apply hS
      · apply ihaA
        apply hS

theorem weakening_sigma_first : 
    ∀ {n : Nat} {Γ : Ctx n} {p A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ p ∶ ΣA;B) →
      (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
          get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ p⌊weaken_from n l⌋ ∶ (ΣA;B)⌊weaken_from n l⌋) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ π₁ p⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋ :=
  by
    intro n Γ p A B hpSi ihpSi l hleq S hS
    apply HasType.sigma_first
    apply ihpSi
    apply hS

theorem weakening_sigma_second :
    ∀ {n : Nat} {Γ : Ctx n} {p A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ p ∶ ΣA;B) →
    (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
        get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ p⌊weaken_from n l⌋ ∶ (ΣA;B)⌊weaken_from n l⌋) →
      ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
        get_sub_context Γ l leq ⊢ B_1 type →
          insert_into_ctx leq Γ B_1 ⊢ π₂ p⌊weaken_from n l⌋ ∶ B⌈π₁ p⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ p A B hpSi ihpSi l hleq S hS
    rw [weak_sub_zero]
    apply HasType.sigma_second
    apply ihpSi
    apply hS

theorem weakening_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
    (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
      (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
        (Γ ⊢ x ∶ 𝒩) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B : Tm l},
              get_sub_context (Γ ⬝ 𝒩) l leq ⊢ B type → insert_into_ctx leq (Γ ⬝ 𝒩) B ⊢ A⌊weaken_from (n + 1) l⌋ type) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type →
                  insert_into_ctx leq Γ B ⊢ z⌊weaken_from n l⌋ ∶ A⌈𝓏⌉₀⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n + 1 + 1} {B : Tm l},
                  get_sub_context (Γ ⬝ 𝒩 ⬝ A) l leq ⊢ B type →
                    insert_into_ctx leq (Γ ⬝ 𝒩 ⬝ A) B ⊢ s⌊weaken_from (n + 1 + 1) l⌋ ∶
                      A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌊weaken_from (n + 1 + 1) l⌋) →
                (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                    get_sub_context Γ l leq ⊢ B type →
                      insert_into_ctx leq Γ B ⊢ x⌊weaken_from n l⌋ ∶ 𝒩⌊weaken_from n l⌋) →
                  ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                    get_sub_context Γ l leq ⊢ B type →
                      insert_into_ctx leq Γ B ⊢ A.indNat z s x⌊weaken_from n l⌋ ∶ A⌈x⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ z i A s hA hzA hsA hiNat ihA ihzA ihsA ihiNat l hleq S hS
    rw [weak_sub_zero]
    apply HasType.nat_elim
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_nat]
      rw [extend_insert_into_context]
      apply ihA
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · simp [lift_weak_n]
      rw [←weakening_nat_zero]
      rw [←weak_sub_zero]
      apply ihzA
      apply hS
    · rw [←helper_weak_nat_succ]
      rw [←weakening_nat]
      rw [extend_insert_into_context]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihsA
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · apply ihiNat
      apply hS

theorem weakening_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ), (v(0)), (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (Γ ⊢ p ∶ a ≃[A] a') →
                (∀ (l : Nat) {leq : l ≤ n + 1 + 1 + 1} {B_1 : Tm l},
                    get_sub_context (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) l leq ⊢ B_1 type →
                      insert_into_ctx leq (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B_1 ⊢
                        B⌊↑₁n + 1 + 1 + 1↬l⌋ type) →
                  (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
                      get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                        insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ b⌊↑₁n + 1↬l⌋ ∶
                          B⌈(ₛidₚ), (v(0)), (A⌊↑ₚidₚ⌋.refl v(0))⌉⌊↑₁n + 1↬l⌋) →
                    (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                        get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) →
                      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a'⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) →
                        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                            get_sub_context Γ l leq ⊢ B type →
                              insert_into_ctx leq Γ B ⊢ p⌊↑₁n↬l⌋ ∶ (a ≃[A] a')⌊↑₁n↬l⌋) →
                              ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                                get_sub_context Γ l leq ⊢ B_1 type →
                                  insert_into_ctx leq Γ B_1 ⊢ A.j B b a a' p⌊↑₁n↬l⌋ ∶ B⌈(ₛidₚ), a, a', p⌉⌊↑₁n↬l⌋ :=
  by
    intro n Γ A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId l hleq S hS
    rw [weak_subst_iden_elim]
    apply HasType.iden_elim
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      rw [←shift_weaken_from]
      rw [extend_insert_into_context]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←shift_weaken_from]
      rw [←shift_weaken_from]
      rw [weakening_shift_id]
      rw [←helper_weak_iden_propagate_weak]
      rw [extend_insert_into_context]
      apply ihB
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · rw [extend_insert_into_context]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [helper_weak_refl_propagate_weak]
      apply ihbB
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · apply ihaA
      apply hS
    · apply ihaA'
      apply hS
    · apply ihpId
      apply hS

theorem weakening_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
    (Γ ⊢ a ∶ A) →
      Γ ⊢ A ≡ B type →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ A⌊weaken_from n l⌋ ≡ B⌊weaken_from n l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ a⌊weaken_from n l⌋ ∶ B⌊weaken_from n l⌋ :=
  by
    intro n Γ a A B haA hAB ihaA ihAB l hleq S hS
    apply HasType.ty_conv
    · apply ihaA
      apply hS
    · apply ihAB
      apply hS
