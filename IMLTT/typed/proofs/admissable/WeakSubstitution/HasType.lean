import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.substitution.Helpers
import IMLTT.typed.proofs.admissable.WeakeningGeneral
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import IMLTT.typed.proofs.admissable.weaksubstitution.Helpers

theorem weak_substitution_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type →
    (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) {S : Tm l}
        (A_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (s : Tm (l + 1)) (S : Tm l)
        (a A_1 : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ v(0) = a →
            eqM ▸ A⌊↑ₚidₚ⌋ = A_1 →
              (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqt
    cases heqT
    cases n with
    | zero =>
      simp [substitute]
      simp [n_substitution_shift]
      simp [substitute_var]
      simp [substitution_comp_σρ]
      simp [comp_substitute_weaken]
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_into_gen_ctx]
        simp [expand_ctx]
        simp [substitution_conv_shift_id_conv]
        apply hsS
      | expand Δ' T =>
        have h1 := gen_ctx_leq Δ'
        omega
    | succ n' =>
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        rw [n_substitution_shift_zero]
        rw [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        simp [substitute]
        simp [substitute_var]
        rw [substitution_conv_shift_id_conv]
        apply hsS
      | expand Δ' T =>
        cases heqΓ
        simp [substitute]
        rw [←lift_n_substitution_shift]
        simp [substitution_shift_id_lift]
        simp [←extend_expand_context_n_substitution_shift]
        rw (config := {occs := .pos [2]}) [n_substitution_shift]
        simp_all
        split
        case isTrue hlt =>
          simp [substitute_var]
          apply HasType.var
          apply ihA
          · rfl
          · apply hsS
          · rfl
        case isFalse hnlt =>
          simp [substitute_var]
          apply HasType.var
          apply ihA
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_weak :
     ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
     (Γ ⊢ v(i) ∶ A) →
       Γ ⊢ B type →
         (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) (S : Tm l)
             (a A_1 : Tm m),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ v(i) = a →
                 eqM ▸ A = A_1 →
                   (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) {S : Tm l}
               (A : Tm m),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ B = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ type) →
             ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (s : Tm (l + 1))
               (S : Tm l) (a A_1 : Tm m),
               eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ v(i)⌊↑ₚidₚ⌋ = a →
                   eqM ▸ A⌊↑ₚidₚ⌋ = A_1 →
                     (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n x Γ' A B hvA hB ihvA ihB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqt
    cases heqT
    cases n with
    | zero =>
      cases Δ with
      | start =>
        cases heqΓ
        simp [n_substitution_shift]
        simp [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        rw [empty_extend_expand_context_n_substitution_shift (Γ := Γ' ⬝ B)]
        rw [empty_expand_context]
        simp [substitution_conv_shift_id_conv]
        apply HasType.weak
        · apply hvA
        · apply hB
      | expand Δ' T =>
        have h1 := gen_ctx_leq Δ'
        omega
    | succ n' =>
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        rw [n_substitution_shift_zero]
        simp [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        simp [substitution_conv_shift_id_conv]
        apply HasType.weak
        · apply hvA
        · apply hB
      | expand Δ' T =>
        cases heqΓ
        rw [←lift_n_substitution_shift]
        simp [substitution_shift_id_lift]
        simp [←extend_expand_context_n_substitution_shift]
        apply weakening_term
        · apply ihvA
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
        · have h := gen_ctx_leq Δ'
          omega

theorem weak_substitution_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ ⋆ = a →
              eqM ▸ 𝟙 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.unit_intro
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · omega
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ∶ B) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1)) (S : Tm l)
          (a A_1 : Tm m),
          eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ b = a →
              eqM ▸ B = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            (eqM ▸ λA; b) = a →
              (eqM ▸ ΠA;B) = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A b B hbB ihbB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.pi_intro
    simp [lift_subst_n]
    simp [lift_n_substitution_shift]
    rw [extend_expand_context_n_substitution_shift]
    apply ihbB
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem weak_substitution_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A) →
      (Γ ⊢ b ∶ B⌈a⌉₀) →
        Γ ⬝ A ⊢ B type →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_5 A : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ b = a_5 →
                    eqM ▸ B⌈a⌉₀ = A →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                  {S : Tm l} (A_1 : Tm m),
                  eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ B = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a_7 A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a&b = a_7 →
                      (eqM ▸ ΣA;B) = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_7⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' a A b B haA hbB hB ihaA ihbB ihB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.sigma_intro
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      simp [←substitution_zero_lift]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihB
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝓏 = a →
              eqM ▸ 𝒩 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.nat_zero_intro
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · omega
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ x = a →
              eqM ▸ 𝒩 = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝓈(x) = a →
              eqM ▸ 𝒩 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' x hxNat ihxNat m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.nat_succ_intro
    rw [←substitution_nat]
    apply ihxNat
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem weak_substitution_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    Γ ⊢ A type →
      (Γ ⊢ a ∶ A) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
            (A_1 : Tm m),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A.refl a = a_5 →
                  (eqM ▸ a ≃[A] a) = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A a hA haA ihA ihaA m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.iden_intro
    · apply ihA
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

theorem weak_substitution_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝟙 = a →
              eqM ▸ 𝒰 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_unit
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · omega
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝟘 = a →
              eqM ▸ 𝒰 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_empty
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · omega
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ∶ 𝒰) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = a →
                eqM ▸ 𝒰 = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (a A_1 : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = a →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΠA;B) = a →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_pi
    · rw [←substitution_univ]
      apply ihAU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_univ]
      simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihBU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ∶ 𝒰) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = a →
                eqM ▸ 𝒰 = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (a A_1 : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = a →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΣA;B) = a →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_sigma
    · rw [←substitution_univ]
      apply ihAU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_univ]
      simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihBU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝒩 = a →
              eqM ▸ 𝒰 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_nat
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · omega
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = a →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_5 A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a = a_5 →
                    eqM ▸ A = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a' = a →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a_7 A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    (eqM ▸ a ≃[A] a') = a_7 →
                      eqM ▸ 𝒰 = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_7⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A a a' hAU haA haA' ihAU ihaA ihaA' m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_iden
    · rw [←substitution_univ]
      apply ihAU
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
    · apply ihaA'
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_unit_elim : 
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type →
      (Γ ⊢ a ∶ A⌈⋆⌉₀) →
        (Γ ⊢ b ∶ 𝟙) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              {S : Tm l} (A_1 : Tm m),
              eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_5 A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a = a_5 →
                    eqM ▸ A⌈⋆⌉₀ = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a A : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ b = a →
                      eqM ▸ 𝟙 = A →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a_7 A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ A.indUnit b a = a_7 →
                      eqM ▸ A⌈b⌉₀ = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_7⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A a b hA haA hb1 ihA ihaA ihb1 m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply HasType.unit_elim
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_unit]
      rw [extend_expand_context_n_substitution_shift]
      apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_tt]
      rw [←substitution_zero_lift]
      apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_unit]
      apply ihb1
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type →
      (Γ ⊢ b ∶ 𝟘) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
            {S : Tm l} (A_1 : Tm m),
            eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ b = a →
                  eqM ▸ 𝟘 = A →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A.indEmpty b = a →
                  eqM ▸ A⌈b⌉₀ = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A b hA hb0 ihA ihb0 m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply HasType.empty_elim
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_empty]
      rw [extend_expand_context_n_substitution_shift]
      apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_empty]
      apply ihb0
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B) →
      (Γ ⊢ a ∶ A) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ f = a →
                (eqM ▸ ΠA;B) = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ f◃a = a_5 →
                  eqM ▸ B⌈a⌉₀ = A →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' f A B a hfPi haA ihfPi ihaA m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitution_zero_lift]
    apply HasType.pi_elim
    · rw [←substitution_pi]
      apply ihfPi
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

theorem weak_substitution_sigma_first :
    ∀ {n : Nat} {Γ : Ctx n} {p A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ p ∶ ΣA;B) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ p = a →
              (eqM ▸ ΣA;B) = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ π₁ p = a →
              eqM ▸ A = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' p A B hpSi ihpSi m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.sigma_first
    rotate_right
    · apply B⌈1ₙ⇑ₛ(s↑/ₙhleq)⌉
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      apply ihpSi
      repeat' rfl
      apply hsS

theorem weak_substitution_sigma_second :
    ∀ {n : Nat} {Γ : Ctx n} {p A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ p ∶ ΣA;B) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ p = a →
              (eqM ▸ ΣA;B) = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ π₂ p = a →
              eqM ▸ B⌈π₁ p⌉₀ = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' p A B hpSi ihpSi m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitution_zero_lift]
    apply HasType.sigma_second
    rotate_right
    · apply A⌈(s↑/ₙhleq)⌉
    · rw [←substitution_sigma]
      apply ihpSi
      repeat' rfl
      apply hsS

theorem weak_substitution_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
      (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
        (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
          (Γ ⊢ x ∶ 𝒩) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                {S : Tm l} (A_1 : Tm m),
                eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ z = a →
                      eqM ▸ A⌈𝓏⌉₀ = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m)
                    (s_1 : Tm (l + 1)) (S : Tm l) (a A_1 : Tm m),
                    eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ s = a →
                        eqM ▸ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                          (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                      (S : Tm l) (a A : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ x = a →
                          eqM ▸ 𝒩 = A →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                    ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s_1 : Tm (l + 1))
                      (S : Tm l) (a A_1 : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ A.indNat z s x = a →
                          eqM ▸ A⌈x⌉₀ = A_1 →
                            (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉ :=
  by
    intro n Γ' z x A s hA hzA hsA hxNat ihA ihzA ihsA ihxNat m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitution_zero_lift]
    apply HasType.nat_elim
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_nat]
      rw [extend_expand_context_n_substitution_shift]
      apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_var_zero]
      rw [←substitution_zero_lift]
      apply ihzA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_nat]
      rw [extend_expand_context_n_substitution_shift]
      simp [lift_subst_n]
      rw [←helper_weak_subst_nat_elim (A := A)]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihsA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
      apply hleq
    · rw [←substitution_nat]
      apply ihxNat
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (Γ ⊢ p ∶ a ≃[A] a') →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 + 1 = m)
                    (s : Tm (l + 1)) {S : Tm l} (A_1 : Tm m),
                    (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ B = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m)
                      (s : Tm (l + 1)) (S : Tm l) (a A_1 : Tm m),
                      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ b = a →
                          eqM ▸ B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1 →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                    (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                        (S : Tm l) (a_8 A_1 : Tm m),
                        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ a = a_8 →
                            eqM ▸ A = A_1 →
                              (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_8⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                          (s : Tm (l + 1)) (S : Tm l) (a A_1 : Tm m),
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                            eqM ▸ a' = a →
                              eqM ▸ A = A_1 →
                                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                            (s : Tm (l + 1)) (S : Tm l) (a_10 A_1 : Tm m),
                            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                              eqM ▸ p = a_10 →
                                (eqM ▸ a ≃[A] a') = A_1 →
                                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_10⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                              ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                                (s : Tm (l + 1)) (S : Tm l) (a_13 A_1 : Tm m),
                                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                  eqM ▸ A.j B b a a' p = a_13 →
                                    eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A_1 →
                                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_13⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    rw [subst_subst_iden_elim]
    apply HasType.iden_elim
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      simp [←substitution_shift_id_lift]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      simp_all
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihB
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_shift_id_lift]
      rw [subst_subst_iden_refl]
      rw [extend_expand_context_n_substitution_shift]
      simp [lift_subst_n]
      rw [lift_n_substitution_shift]
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
    · apply ihaA'
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_iden]
      apply ihpId
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
    (Γ ⊢ a ∶ A) →
      Γ ⊢ A ≡ B type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a_3 A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ a = a_3 →
                eqM ▸ A = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_3⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A' : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ B = A' →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_5 →
                  eqM ▸ B = A →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' a A B haA hAB ihaA ihAB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply HasType.ty_conv
    · apply ihaA
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

