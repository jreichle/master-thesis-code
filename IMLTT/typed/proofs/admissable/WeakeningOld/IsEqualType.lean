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

theorem weakening_unit_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝟙⌊weaken_from n l⌋ ≡ 𝟙⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq S hS
    apply IsEqualType.unit_form_eq
    apply ihiC
    apply hS

theorem weakening_empty_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝟘⌊weaken_from n l⌋ ≡ 𝟘⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq S hS
    apply IsEqualType.empty_form_eq
    apply ihiC
    apply hS

theorem weakening_pi_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ≡ B'⌊weaken_from (n + 1) l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (ΠA;B)⌊weaken_from n l⌋ ≡ (ΠA';B')⌊weaken_from n l⌋ type :=
  by
    intro n Γ A A' B B' hAA hBB ihAA ihBB l hleq S hS
    apply IsEqualType.pi_form_eq
    · apply ihAA
      apply hS
    · rw [extend_insert_into_context]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      · apply ihBB
        rw [extend_get_sub_context]
        apply hS
      · exact hleq

theorem weakening_sigma_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ≡ B'⌊weaken_from (n + 1) l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (ΣA;B)⌊weaken_from n l⌋ ≡ (ΣA';B')⌊weaken_from n l⌋ type :=
  by
    intro n Γ A A' B B' hAA hBB ihAA ihBB l hleq S hS
    apply IsEqualType.sigma_form_eq
    · apply ihAA
      apply hS
    · rw [extend_insert_into_context]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      · apply ihBB
        rw [extend_get_sub_context]
        apply hS
      · exact hleq

theorem weakening_nat_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
      ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
        get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝒩⌊weaken_from n l⌋ ≡ 𝒩⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq S hS
    apply IsEqualType.nat_form_eq
    apply ihiC
    apply hS

theorem weakening_iden_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ A' : Tm n},
    Γ ⊢ A ≡ A' type →
      (Γ ⊢ a₁ ≡ a₂ ∶ A) →
        (Γ ⊢ a₃ ≡ a₄ ∶ A') →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type →
                  insert_into_ctx leq Γ B ⊢ a₁⌊weaken_from n l⌋ ≡ a₂⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ a₃⌊weaken_from n l⌋ ≡ a₄⌊weaken_from n l⌋ ∶ A'⌊weaken_from n l⌋) →
                ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ (a₁ ≃[A] a₃)⌊weaken_from n l⌋ ≡ (a₂ ≃[A'] a₄)⌊weaken_from n l⌋ type :=
  by
    intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA' l hleq S hS
    apply IsEqualType.iden_form_eq
    · apply ihAA
      apply hS
    · apply ihaaA
      apply hS
    · apply ihaaA'
      apply hS

theorem weakening_univ_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ 𝒰⌊weaken_from n l⌋ ≡ 𝒰⌊weaken_from n l⌋ type :=
  by
    intro n Γ hiC ihiC l hleq S hS
    apply IsEqualType.univ_form_eq
    apply ihiC
    apply hS

theorem weakening_univ_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type →
            insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type :=
  by
    intro n Γ A A' hAAU ihAAU l hleq S hS
    apply IsEqualType.univ_elim_eq
    apply ihAAU
    apply hS

theorem weakening_type_symm :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    Γ ⊢ A ≡ A' type →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A'⌊weaken_from n l⌋ ≡ A⌊weaken_from n l⌋ type :=
  by
    intro n Γ A A' hAA ihAA l hleq S hS
    apply IsEqualType.type_symm
    apply ihAA
    apply hS

theorem weakening_type_trans :
∀ {n : Nat} {Γ : Ctx n} {A B C : Tm n},
Γ ⊢ A ≡ B type →
  Γ ⊢ B ≡ C type →
    (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
        get_sub_context Γ l leq ⊢ B_1 type →
          insert_into_ctx leq Γ B_1 ⊢ A⌊weaken_from n l⌋ ≡ B⌊weaken_from n l⌋ type) →
      (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
          get_sub_context Γ l leq ⊢ B_1 type →
            insert_into_ctx leq Γ B_1 ⊢ B⌊weaken_from n l⌋ ≡ C⌊weaken_from n l⌋ type) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ C⌊weaken_from n l⌋ type :=
  by
    intro n Γ A B C hAB hBC ihAB ihBC l hleq S hS
    apply IsEqualType.type_trans
    · apply ihAB
      apply hS
    · apply ihBC
      apply hS

