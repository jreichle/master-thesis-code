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
import IMLTT.typed.proofs.admissable.weakening.WeakeningGeneral

theorem weak_substitution_unit_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
        (A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟙 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.unit_form
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
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_empty_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
        (A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟘 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.empty_form
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
          · rfl
          · apply hsS
          · rfl


theorem weak_substitution_pi_form :
  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
  Γ ⊢ A type →
    Γ ⬝ A ⊢ B type →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
          (A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
            {S : Tm l} (A_1 : Tm m),
            eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ B = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
          ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
            (A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              (eqM ▸ ΠA;B) = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A B hA hB ihA ihB m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsType.pi_form
    · apply ihA
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

theorem weak_substitution_sigma_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type →
      Γ ⬝ A ⊢ B type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
            (A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              {S : Tm l} (A_1 : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
              (A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΣA;B) = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A B hA hB ihA ihB m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsType.sigma_form
    · apply ihA
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

theorem weak_substitution_nat_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
        (A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝒩 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.nat_form
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
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_iden_form :
    ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
    Γ ⊢ A type →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
              (A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
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
                  {S : Tm l} (A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    (eqM ▸ a ≃[A] a') = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' a A a' hA haA haA' ihA ihaA ihaA' m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.iden_form
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
    · apply ihaA'
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_univ_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
        (A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝒰 = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_form
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
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    (Γ ⊢ A ∶ 𝒰) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = a →
              eqM ▸ 𝒰 = A_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) {S : Tm l}
          (A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A hAU ihAU m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_elim
    rw [←substitution_univ]
    apply ihAU
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl
