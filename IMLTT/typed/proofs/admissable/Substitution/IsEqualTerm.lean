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
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.DefeqRefl

import IMLTT.typed.proofs.admissable.substitution.Helpers

theorem substitution_gen_var_eq : ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
   Γ ⊢ A type →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
         (A_1 : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l)
         (a a' A_1 : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ v(0) = a →
             eqM ▸ v(0) = a' →
               eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases Δ with
    | start =>
      have h := defeq_refl_term hsS
      replace_by_conclusion h
      · substitution_step
      · apply h
    | expand Δ' S' =>
      cases heqΓ
      cases n with
      | zero =>
        cases hleq
        replace_by_conclusion hsS
        · apply congr
          · substitution_step
          · substitution_step
        · apply hsS
      | succ n' =>
        replace_by_conclusion IsEqualTerm.var_eq
        · apply congr
          · substitution_step
          · substitution_step
        · apply IsEqualTerm.var_eq
          apply ihA
          repeat' rfl
          apply hsS

theorem substitution_gen_weak_eq : ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
   (Γ ⊢ v(i) ≡ v(i) ∶ A) →
     Γ ⊢ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ v(i) = a →
               eqM ▸ v(i) = a' →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
             (A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ v(i)⌊↑ₚidₚ⌋ = a →
                 eqM ▸ v(i)⌊↑ₚidₚ⌋ = a' →
                   eqM ▸ A⌊↑ₚidₚ⌋ = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n x Γ' A B hvvA hB ihvvA ihB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases n
    case zero =>
      simp [n_substitution]
      cases Δ with
      | start =>
        cases heqΓ
        replace_by_conclusion hvvA
        · substitution_step
        · apply hvvA
      | expand Δ' T =>
        have h := gen_ctx_neq Δ'
        omega
    case succ n' =>
      simp [n_substitution]
      split
      case isTrue hT =>
        cases Δ with
        | start =>
          omega
        | expand Δ' T =>
          cases heqΓ
          have h := gen_ctx_leq Δ'
          replace_by_conclusion weakening_term_eq
          · apply congr
            apply congr
            · rfl
            · substitution_step
            · substitution_step
              rw [←substitution_conv_shift_id]
          · apply weakening_term_eq
            · rw [←substitution_conv_var]
              apply ihvvA
              · rfl
              · rfl
              · rfl
              · rfl
              · apply hsS
              · rfl
            · apply ihB
              · rfl
              · rfl
              · apply hsS
              · rfl
      case isFalse hF =>
        cases Δ with
        | start =>
          cases heqΓ
          replace_by_conclusion hvvA
          · substitution_step
          · apply hvvA
        | expand Δ' T =>
          have h := gen_ctx_leq Δ'
          omega

theorem substitution_gen_unit_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
   Γ ⬝ 𝟙 ⊢ A type →
     (Γ ⊢ a ∶ A⌈⋆⌉₀) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
           (A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ A⌈⋆⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A.indUnit ⋆ a = a_5 →
                 eqM ▸ a = a' →
                   eqM ▸ A⌈⋆⌉₀ = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ A a hA haA ihA ihaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.unit_comp
    · replace_by_conclusion ihA
      · apply congr
        apply congr
        · rfl
        · rw [←substitution_unit]
          rw [extend_expand_context_n_substitution]
        · substitution_step
      · apply ihA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihaA
      · apply congr
        apply congr
        · rfl
        · rfl
        · simp only [lift_subst_n]
          rw [←substitution_tt]
          rw [←substitution_zero_lift]
      · apply ihaA
        repeat' rfl
        apply hsS

theorem substitution_gen_pi_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
   (Γ ⬝ A ⊢ b ∶ B) →
     (Γ ⊢ a ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
           (a A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ b = a → eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ (λA; b)◃a = a_5 →
                 eqM ▸ b⌈a⌉₀ = a' →
                   eqM ▸ B⌈a⌉₀ = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A b B a hbB haA ihbB ihaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    rw [substitution_zero_lift]
    apply IsEqualTerm.pi_comp
    · replace_by_conclusion ihbB
      · apply congr
        apply congr
        · rw [extend_expand_context_n_substitution]
        · substitution_step
        · rw [lift_n_substitution]
      · apply ihbB
        repeat' rfl
        apply hsS
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_sigma_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
  (Γ ⬝ ΣA;B) ⊢ C type →
    (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ b ∶ B⌈a⌉₀) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
              (A_1 : Tm (m + 1 - 1 + 1)),
              (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ C = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                (s S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ c = a →
                    eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1 →
                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                  (a_7 A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a = a_7 →
                      eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (a_8 A : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ b = a_8 →
                        eqM ▸ B⌈a⌉₀ = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_8⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (a_9 a' A_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.indSigma B C c (a&b) = a_9 →
                        eqM ▸ c⌈(ₛidₚ)⋄ a⋄ b⌉ = a' →
                          eqM ▸ C⌈a&b⌉₀ = A_1 →
                            (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_9⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A b B C c hC hcC haA hbB ihC ihcC ihaA ihbB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    rw [helper_substitution_sigma_elim_c]
    apply IsEqualTerm.sigma_comp
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihC
      · rfl
      · rfl
      · apply hsS
      · rfl
    · replace_by_conclusion ihcC
      · apply congr
        apply congr
        · simp []
          rw [lift_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · simp only [lift_subst_n]
          rw [helper_substitution_sigma_elim_C]
          rw [lift_n_substitution]
          rw [lift_n_substitution]
      · apply ihcC
        · rfl
        · rfl
        · rfl
        · apply hsS
        · rfl
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp only [lift_subst_n]
      rw [←substitution_zero_lift]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_nat_zero_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
    (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
      (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
        (Γ ⊢ 𝓏 ∶ 𝒩) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
              (A_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (a A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ z = a →
                    eqM ▸ A⌈𝓏⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                  (s_1 S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ s = a →
                      eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                        (Γ_1 ⊢ s_1 ∶ S) → Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (a A : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ 𝓏 = a →
                        eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                    (s_1 S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.indNat z s 𝓏 = a →
                        eqM ▸ z = a' →
                          eqM ▸ A⌈𝓏⌉₀ = A_1 →
                            (Γ_1 ⊢ s_1 ∶ S) →
                              Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ≡ a'⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉ :=
  by
    intro n Γ' z A s hA hzA hsA hzNat ihA ihzA ihsA ihzNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.nat_zero_comp
    · replace_by_conclusion ihA
      · apply congr
        apply congr
        · rfl
        · rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
        · substitution_step
      · apply ihA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihzA
      · apply congr
        apply congr
        · rfl
        · substitution_step
        · simp only [lift_subst_n]
          rw [←substitution_var_zero]
          rw [←substitution_zero_lift]
      · apply ihzA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihsA
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
          rw [lift_n_substitution]
          rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · context_info_nat_relations
          simp only [lift_subst_n]
          rw [←helper_substitution_nat_elim]
          simp only [lift_n_substitution]
          rfl
      · apply ihsA
        repeat' rfl
        apply hsS
    · rw [←substitution_nat]
      rw [←substitution_var_zero]
      apply ihzNat
      · apply hleq
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_nat_succ_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
      (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
        (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
          (Γ ⊢ x ∶ 𝒩) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
                (A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                  (a A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ z = a →
                      eqM ▸ A⌈𝓏⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                    (s_1 S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ s = a →
                        eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                          (Γ_1 ⊢ s_1 ∶ S) → Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉) →
                  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                      (a A : Tm (m + 1 - 1 + 1)),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ x = a →
                          eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
                    ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                      (s_1 S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ A.indNat z s 𝓈(x) = a →
                          eqM ▸ s⌈(ₛidₚ)⋄ x⋄ A.indNat z s x⌉ = a' →
                            eqM ▸ A⌈𝓈(x)⌉₀ = A_1 →
                              (Γ_1 ⊢ s_1 ∶ S) →
                                Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ≡ a'⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉ :=
  by
    intro n Γ' z x A s hA hzA hsA hsNat ihA ihzA ihsA ihsNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    rw [helper_substitution_sigma_elim_c]
    apply IsEqualTerm.nat_succ_comp
    · replace_by_conclusion ihA
      · apply congr
        apply congr
        · rfl
        · rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
        · substitution_step
      · apply ihA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihzA
      · apply congr
        apply congr
        · rfl
        · substitution_step
        · simp only [lift_subst_n]
          rw [←substitution_var_zero]
          rw [←substitution_zero_lift]
      · apply ihzA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihsA
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
          rw [lift_n_substitution]
          rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · context_info_nat_relations
          simp only [lift_subst_n]
          rw [←helper_substitution_nat_elim]
          simp only [lift_n_substitution]
          rfl
      · apply ihsA
        repeat' rfl
        apply hsS
    · rw [←substitution_nat]
      apply ihsNat
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      (Γ ⊢ a ∶ A) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 + 1 = m + 1)
              {s S : Tm l} (A_1 : Tm (m + 1 - 1 + 1)),
              (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
                (a A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ b = a →
                    eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1 →
                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                  (a_7 A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a = a_7 →
                      eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (a_9 a' A_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.j B b a a (A.refl a) = a_9 →
                        eqM ▸ b⌈a⌉₀ = a' →
                          eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a⋄ A.refl a⌉ = A_1 →
                            (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_9⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B b a hB hbB haA ihB ihbB ihaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [helper_substitution_iden_B]
    rw [substitution_zero_lift]
    apply IsEqualTerm.iden_comp
    · context_info_nat_relations
      simp only [lift_subst_n]
      simp only [lift_n_substitution]
      simp only [←substitution_shift_id_lift]
      simp only [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_substitution_iden_propagate_subst]
      simp only [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihB
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_shift_id_lift]
      rw [helper_substitution_iden_B_refl]
      rw [extend_expand_context_n_substitution]
      simp [lift_subst_n]
      rw [lift_n_substitution]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_unit_intro_eq : ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ ⋆ = a →
            eqM ▸ ⋆ = a' →
              eqM ▸ 𝟙 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.unit_intro_eq
    cases Δ
    case start =>
      exact ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_unit_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
   Γ ⬝ 𝟙 ⊢ A ≡ A' type →
     (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀) →
       (Γ ⊢ b ≡ b' ∶ 𝟙) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = A_1 →
                 eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a_5 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = a_5 →
                   eqM ▸ a' = a'_1 →
                     eqM ▸ A⌈⋆⌉₀ = A_1 →
                       (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = a →
                     eqM ▸ b' = a' →
                       eqM ▸ 𝟙 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a_7 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A.indUnit b a = a_7 →
                     eqM ▸ A'.indUnit b' a' = a'_1 →
                       eqM ▸ A⌈b⌉₀ = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.unit_elim_eq
    · replace_by_conclusion ihAA
      · apply congr
        apply congr
        apply congr
        · rfl
        · rw [←substitution_unit]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · substitution_step
      · apply ihAA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihaaA
      · apply congr
        apply congr
        · rfl
        · rfl
        · simp only [lift_subst_n]
          rw [←substitution_tt]
          rw [←substitution_zero_lift]
      · apply ihaaA
        repeat' rfl
        apply hsS
    · rw [←substitution_unit]
      apply ihbb1
      repeat' rfl
      apply hsS

theorem substitution_gen_empty_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
  Γ ⬝ 𝟘 ⊢ A ≡ A' type →
    (Γ ⊢ b ≡ b' ∶ 𝟘) →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
          (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
          eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 →
              eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a a' A : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ b = a →
                eqM ▸ b' = a' →
                  eqM ▸ 𝟘 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a a' A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A.indEmpty b = a →
                eqM ▸ A'.indEmpty b' = a' →
                  eqM ▸ A⌈b⌉₀ = A_1 →
                    (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' b b' hAA hbb0 ihAA ihbb0 m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.empty_elim_eq
    · replace_by_conclusion ihAA
      · apply congr
        apply congr
        apply congr
        · rfl
        · rw [←substitution_empty]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · substitution_step
      · apply ihAA
        repeat' rfl
        apply hsS
    · rw [←substitution_empty]
      apply ihbb0
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_pi_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) →
      Γ ⊢ A ≡ A' type →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
            (a a' A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ b = a →
                eqM ▸ b' = a' →
                  eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (a a' A_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ λA; b) = a →
                  (eqM ▸ λA'; b') = a' →
                    (eqM ▸ ΠA;B) = A_1 →
                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' b b' B hbbB hPiPi ihbbB ihPiPi m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.pi_intro_eq
    · replace_by_conclusion ihbbB
      · apply congr
        apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
        any_goals rw [lift_n_substitution]
      · apply ihbbB
        repeat' rfl
        apply hsS
    · apply ihPiPi
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_pi_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
   (Γ ⊢ f ≡ f' ∶ ΠA;B) →
     (Γ ⊢ a ≡ a' ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ f = a →
               eqM ▸ f' = a' →
                 (eqM ▸ ΠA;B) = A_1 →
                   (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ a' = a'_1 →
                   eqM ▸ A = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a'_1 A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ f◃a = a_5 →
                 eqM ▸ f'◃a' = a'_1 →
                   eqM ▸ B⌈a⌉₀ = A →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' f f' A B a a' hffPi haaA ihffPi ihaaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.pi_elim_eq
    · rw [←substitution_pi]
      apply ihffPi
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
  (Γ ⊢ a ≡ a' ∶ A) →
    (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀) →
      Γ ⬝ A ⊢ B type →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a_4 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ a = a_4 →
                eqM ▸ a' = a'_1 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (a_5 a' A : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ b = a_5 →
                  eqM ▸ b' = a' →
                    eqM ▸ B⌈a⌉₀ = A →
                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
                (A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (a_7 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a&b = a_7 →
                    eqM ▸ a'&b' = a'_1 →
                      (eqM ▸ ΣA;B) = A_1 →
                        (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' a a' A b b' B haaA hbbB hB ihaaA ihbbB ihB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · replace_by_conclusion ihbbB
      · apply congr
        apply congr
        apply congr
        apply congr
        · rfl
        · rfl
        · rfl
        · rfl
        · rw [←substitution_zero_lift]
      · apply ihbbB
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihB
      · apply congr
        apply congr
        · rfl
        · substitution_step
        · rw [lift_n_substitution]
      · apply ihB
        repeat' rfl
        apply hsS

theorem substitution_gen_sigma_elim_eq : 
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
  {c c' : Tm (n + 1 + 1)},
  (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
    (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉) →
      Γ ⊢ A ≡ A' type →
        Γ ⬝ A ⊢ B ≡ B' type →
          (Γ ⊢ p ≡ p' ∶ ΣA;B) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
                (A_1 A' : Tm (m + 1 - 1 + 1)),
                (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ C = A_1 →
                    eqM ▸ C' = A' → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                  (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ c = a →
                      eqM ▸ c' = a' →
                        eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1 →
                          (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A = A_1 →
                        eqM ▸ A' = A'_1 →
                          (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
                  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1)
                      (s S : Tm l) (A_1 A' : Tm (m + 1 - 1 + 1)),
                      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ B = A_1 →
                          eqM ▸ B' = A' →
                            (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
                    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                        (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ p = a →
                            eqM ▸ p' = a' →
                              (eqM ▸ ΣA;B) = A_1 →
                                (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                        (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ A.indSigma B C c p = a →
                            eqM ▸ A'.indSigma B' C' c' p' = a' →
                              eqM ▸ C⌈p⌉₀ = A_1 →
                                (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B A' B' p p' C C' c c' hCC hccC hAA hBB hppSi ihCC ihccC ihAA ihBB ihppSi  m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.sigma_elim_eq
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihCC
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · replace_by_conclusion ihccC
      · apply congr
        apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
          rw [lift_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · substitution_step
        · simp only [lift_subst_n]
          rw [helper_substitution_sigma_elim_C]
          context_info_nat_relations
          simp only [lift_n_substitution]
          rfl
      · apply ihccC
        repeat' rfl
        apply hsS
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp only [lift_subst_n]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihBB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      apply ihppSi
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_nat_zero_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝓏 = a →
            eqM ▸ 𝓏 = a' →
              eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_zero_intro_eq
    simp_all
    cases Δ
    case start =>
      exact ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_nat_succ_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {x x' : Tm n},
    (Γ ⊢ x ≡ x' ∶ 𝒩) →
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ x = a →
            eqM ▸ x' = a' →
              eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝓈(x) = a →
            eqM ▸ 𝓈(x') = a' →
              eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' x x' hxxNat ihxxNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_succ_intro_eq
    rw [←substitution_nat]
    apply ihxxNat
    · rfl
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_nat_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {z z' x x' : Tm n} {A A' : Tm (n + 1)} {s s' : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A ≡ A' type →
    (Γ ⊢ z ≡ z' ∶ A⌈𝓏⌉₀) →
      (Γ ⬝ 𝒩 ⬝ A ⊢ s ≡ s' ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
        (Γ ⊢ x ≡ x' ∶ 𝒩) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
              (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (a a' A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ z = a →
                    eqM ▸ z' = a' →
                      eqM ▸ A⌈𝓏⌉₀ = A_1 →
                        (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                  (s_1 S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ s = a →
                      eqM ▸ s' = a' →
                        eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                          (Γ_1 ⊢ s_1 ∶ S) →
                            Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ≡ a'⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (a a' A : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ x = a →
                        eqM ▸ x' = a' →
                          eqM ▸ 𝒩 = A →
                            (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                    (s_1 S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.indNat z s x = a →
                        eqM ▸ A'.indNat z' s' x' = a' →
                          eqM ▸ A⌈x⌉₀ = A_1 →
                            (Γ_1 ⊢ s_1 ∶ S) →
                              Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ≡ a'⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉ :=
  by
    intro n Γ' z z' x x' A A' s s' hAA hzzA hssA hxxNat ihAA ihzzA ihssA ihxxNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.nat_elim_eq
    · replace_by_conclusion ihAA
      · apply congr
        apply congr
        apply congr
        · rfl
        · rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · substitution_step
      · apply ihAA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihzzA
      · apply congr
        apply congr
        · rfl
        · substitution_step
        · simp only [lift_subst_n]
          rw [←substitution_var_zero]
          rw [←substitution_zero_lift]
      · apply ihzzA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihssA
      · apply congr
        apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
          rw [lift_n_substitution]
          rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · substitution_step
        · context_info_nat_relations
          simp only [lift_subst_n]
          rw [←helper_substitution_nat_elim]
          simp only [lift_n_substitution]
          rfl
      · apply ihssA
        repeat' rfl
        apply hsS
    · rw [←substitution_nat]
      apply ihxxNat
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
   Γ ⊢ A ≡ A' type →
     (Γ ⊢ a ≡ a' ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = A_1 →
               eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ a' = a'_1 →
                   eqM ▸ A = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A.refl a = a_5 →
                 eqM ▸ A'.refl a' = a'_1 →
                   (eqM ▸ a ≃[A] a) = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' a a' hAA haaA ihAA ihaaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.iden_intro_eq
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_elim_eq :
  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' : Tm (n + 1)} {a₁ a₃ A' a₂ a₄ p p' : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type →
    (Γ ⬝ A ⊢ b ≡ b' ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      Γ ⊢ A ≡ A' type →
        (Γ ⊢ a₁ ≡ a₂ ∶ A) →
          (Γ ⊢ a₃ ≡ a₄ ∶ A') →
            (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃) →
                  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 + 1 = m + 1)
                      (s S : Tm l) (A_1 A' : Tm (m + 1 - 1 + 1)),
                      (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ B = A_1 →
                          eqM ▸ B' = A' →
                            (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
                    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1)
                        (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                        eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ b = a →
                            eqM ▸ b' = a' →
                              eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1 →
                                (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                          (s S : Tm l) (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                            eqM ▸ A = A_1 →
                              eqM ▸ A' = A'_1 →
                                (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
                        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                            (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                              eqM ▸ a₁ = a →
                                eqM ▸ a₂ = a' →
                                  eqM ▸ A = A_1 →
                                    (Γ_1 ⊢ s ∶ S) →
                                      Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                              (s S : Tm l) (a a' A : Tm (m + 1 - 1 + 1)),
                              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                eqM ▸ a₃ = a →
                                  eqM ▸ a₄ = a' →
                                    eqM ▸ A' = A →
                                      (Γ_1 ⊢ s ∶ S) →
                                        Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
                            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                                (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                  eqM ▸ p = a →
                                    eqM ▸ p' = a' →
                                      (eqM ▸ a₁ ≃[A] a₃) = A_1 →
                                        (Γ_1 ⊢ s ∶ S) →
                                          Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                                  ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
                                    (eqM : n = m + 1) (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                      eqM ▸ A.j B b a₁ a₃ p = a →
                                        eqM ▸ A'.j B' b' a₂ a₄ p' = a' →
                                          eqM ▸ B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉ = A_1 →
                                            (Γ_1 ⊢ s ∶ S) →
                                              Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hAA haaA haaA' hppId ihBB ihbbB ihAA ihaaA ihaaA' ihppId
    intro m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [helper_substitution_iden_B]
    apply IsEqualTerm.iden_elim_eq
    · context_info_nat_relations
      simp only [lift_subst_n]
      simp only [lift_n_substitution]
      simp only [←substitution_shift_id_lift]
      simp only [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_substitution_iden_propagate_subst]
      simp only [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihBB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_shift_id_lift]
      rw [helper_substitution_iden_B_refl]
      rw [extend_expand_context_n_substitution]
      simp [lift_subst_n]
      rw [lift_n_substitution]
      apply ihbbB
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA'
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_iden]
      apply ihppId
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_unit_eq : ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟙 = a →
            eqM ▸ 𝟙 = a' →
              eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_unit_eq
    apply ihiC
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_empty_eq : ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟘 = a →
            eqM ▸ 𝟘 = a' →
              eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_empty_eq
    apply ihiC
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_pi_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
   (Γ ⊢ A ≡ A' ∶ 𝒰) →
     (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = a →
               eqM ▸ A' = a' →
                 eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ B = a →
                 eqM ▸ B' = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               (eqM ▸ ΠA;B) = a →
                 (eqM ▸ ΠA';B') = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_pi_eq
    · rw [←substitution_univ]
      apply ihAAU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp only [lift_subst_n]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [←substitution_univ]
      apply ihBBU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_sigma_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
   (Γ ⊢ A ≡ A' ∶ 𝒰) →
     (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = a →
               eqM ▸ A' = a' →
                 eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ B = a →
                 eqM ▸ B' = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               (eqM ▸ ΣA;B) = a →
                 (eqM ▸ ΣA';B') = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_sigma_eq
    · rw [←substitution_univ]
      apply ihAAU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp only [lift_subst_n]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [←substitution_univ]
      apply ihBBU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_nat_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a a' A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝒩 = a →
            eqM ▸ 𝒩 = a' →
              eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_nat_eq
    apply ihiC
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_iden_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
   (Γ ⊢ A ≡ A' ∶ 𝒰) →
     (Γ ⊢ a₁ ≡ a₂ ∶ A) →
       (Γ ⊢ a₃ ≡ a₄ ∶ A) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = a →
                 eqM ▸ A' = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a a' A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a₁ = a →
                   eqM ▸ a₂ = a' →
                     eqM ▸ A = A_1 →
                       (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a₃ = a →
                     eqM ▸ a₄ = a' →
                       eqM ▸ A = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   (eqM ▸ a₁ ≃[A] a₃) = a →
                     (eqM ▸ a₂ ≃[A'] a₄) = a' →
                       eqM ▸ 𝒰 = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_iden_eq
    · rw [←substitution_univ]
      apply ihAAU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA'
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_ty_conv_eq : ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
   (Γ ⊢ a ≡ b ∶ A) →
     Γ ⊢ A ≡ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a_3 a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ a = a_3 →
               eqM ▸ b = a' →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_3⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (A_1 A' : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = A_1 →
                 eqM ▸ B = A' → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a' A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_5 →
                 eqM ▸ b = a' →
                   eqM ▸ B = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' a b A B habA hAB ihabA ihAB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.ty_conv_eq
    · apply ihabA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihAB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_term_symm : ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
  (Γ ⊢ a ≡ a' ∶ A) →
  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
      (a_1 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
        eqM ▸ a = a_1 →
          eqM ▸ a' = a'_1 →
            eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_1⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
    ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
      (a_2 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
        eqM ▸ a' = a_2 →
          eqM ▸ a = a'_1 →
            eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_2⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' a a' A haaA ihaaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_symm
    apply ihaaA
    · rfl
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_term_trans : ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
 (Γ ⊢ a ≡ b ∶ T) →
   (Γ ⊢ b ≡ c ∶ T) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
         (a_1 a' A : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ a = a_1 →
             eqM ▸ b = a' →
               eqM ▸ T = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_1⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ b = a →
               eqM ▸ c = a' →
                 eqM ▸ T = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a_3 a' A : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ a = a_3 →
               eqM ▸ c = a' →
                 eqM ▸ T = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_3⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' S a b c habT hbcT ihabT ihbcT m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_trans
    · apply ihabT
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihbcT
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
