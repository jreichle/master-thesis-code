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
import IMLTT.typed.proofs.admissable.WeakeningGeneral

theorem weak_substitution_unit_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A A' : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝟙 = A →
              eqM ▸ 𝟙 = A' →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.unit_form_eq
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

theorem weak_substitution_empty_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A A' : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝟘 = A →
              eqM ▸ 𝟘 = A' →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.empty_form_eq
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

theorem weak_substitution_pi_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (A_1 A'_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 →
                eqM ▸ A' = A'_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (A_1 A' : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A_1 →
                  eqM ▸ B' = A' →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A'_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΠA;B) = A_1 →
                  (eqM ▸ ΠA';B') = A'_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A A' B B' hAA hBB ihAA ihBB m l hleq Γ Δ heqM s S T T' heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    simp [substitute]
    apply IsEqualType.pi_form_eq
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihBB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_sigma_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (A_1 A'_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 →
                eqM ▸ A' = A'_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (A_1 A' : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A_1 →
                  eqM ▸ B' = A' →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A'_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΣA;B) = A_1 →
                  (eqM ▸ ΣA';B') = A'_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A A' B B' hAA hBB ihAA ihBB m l hleq Γ Δ heqM s S T T' heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    simp [substitute]
    apply IsEqualType.sigma_form_eq
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihBB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_nat_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A A' : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝒩 = A →
              eqM ▸ 𝒩 = A' →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.nat_form_eq
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

theorem weak_substitution_iden_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ A' : Tm n},
    Γ ⊢ A ≡ A' type →
      (Γ ⊢ a₁ ≡ a₂ ∶ A) →
        (Γ ⊢ a₃ ≡ a₄ ∶ A') →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A'_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ A' = A'_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a a' A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a₁ = a →
                    eqM ▸ a₂ = a' →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a a' A : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a₃ = a →
                      eqM ▸ a₄ = a' →
                        eqM ▸ A' = A →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (A_1 A'_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    (eqM ▸ a₁ ≃[A] a₃) = A_1 →
                      (eqM ▸ a₂ ≃[A'] a₄) = A'_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA' m l hleq Γ Δ heqM s S T T' heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    simp [substitute]
    apply IsEqualType.iden_form_eq
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

theorem weak_substitution_univ_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A A' : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝒰 = A →
              eqM ▸ 𝒰 = A' →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.univ_form_eq
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

theorem weak_substitution_univ_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a a' A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = a →
              eqM ▸ A' = a' →
                eqM ▸ 𝒰 = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A_1 A'_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 →
              eqM ▸ A' = A'_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A A' hAAU ihAAU m l hleq Γ Δ heqM s S T T' heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.univ_elim_eq
    rw [←substitution_univ]
    apply ihAAU
    · rfl
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem weak_substitution_type_symm :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    Γ ⊢ A ≡ A' type →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A_1 A'_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 →
              eqM ▸ A' = A'_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (A_1 A'_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A' = A_1 →
              eqM ▸ A = A'_1 →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A A' hAA ihAA m l hleq Γ Δ heqM s S T T' heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.type_symm
    apply ihAA
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem weak_substitution_type_trans :
    ∀ {n : Nat} {Γ : Ctx n} {A B C : Tm n},
    Γ ⊢ A ≡ B type →
      Γ ⊢ B ≡ C type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (A_1 A' : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 →
                eqM ▸ B = A' →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A A' : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A →
                  eqM ▸ C = A' →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A' : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ C = A' →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type :=
  by
    intro n Γ' A B C hAB hBC ihAB ihBC m l hleq Γ Δ heqM s S T T' heqΓ heqT heqT' hsS
    cases heqM
    cases heqΓ
    cases heqT
    cases heqT'
    apply IsEqualType.type_trans
    · apply ihAB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihBC
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
