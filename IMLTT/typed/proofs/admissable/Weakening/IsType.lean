import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem weakening_unit_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝟙⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply IsType.unit_form
    apply ihiC
    apply hB

theorem weakening_empty_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝟘⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply IsType.empty_form
    apply ihiC
    apply hB

theorem weakening_pi_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type →
      Γ ⬝ A ⊢ B type →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ (ΠA;B)⌊weaken_from n l⌋ type :=
  by
    intro n Γ A B hA hB ihA ihB l hleq S hS
    simp [weaken]
    simp [lift_weak_n]
    apply IsType.pi_form
    · apply ihA
      · apply hS
    · rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihB
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega

theorem weakening_sigma_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type →
      Γ ⬝ A ⊢ B type →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ (ΣA;B)⌊weaken_from n l⌋ type :=
  by
    intro n Γ A B hA hB ihA ihB l hleq S hS
    simp [weaken]
    simp [lift_weak_n]
    apply IsType.sigma_form
    · apply ihA
      · apply hS
    · rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihB
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega

theorem weakening_iden_form :
    ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
    Γ ⊢ A type →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ type) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
                ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ (a ≃[A] a')⌊weaken_from n l⌋ type :=
  by
    intro n Γ a A a' hA haA haA' ihA ihaA ihaA' l hleq B hB
    simp [weaken]
    apply IsType.iden_form
    · apply ihA
      apply hB
    · apply ihaA
      apply hB
    · apply ihaA'
      apply hB

theorem weakening_univ_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝒰⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq B hB
    simp [weaken]
    apply IsType.univ_form
    apply ihiC
    apply hB

theorem weakening_univ_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    (Γ ⊢ A ∶ 𝒰) →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ type :=
  by
    intro n Γ A hAU ihAU l hleq B hB
    apply IsType.univ_elim
    simp [weaken] at ihAU
    apply ihAU
    apply hB
