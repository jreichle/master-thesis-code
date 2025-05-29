import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts

import IMLTT.typed.JudgmentsAndRules

theorem functionality_typing_empty :
  ∀ (m l k : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : 0 = k + 1)
    (s s' S : Tm l) (T : Tm (m + 1)),
  (Γ ⊢ s ≡ s' ∶ S)
  → (Γ ⊢ s ∶ S)
  → (Γ ⊢ s' ∶ S)
  → eqM ▸ ε = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
  → Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type
      :=
  by
    intro m l hleq Γ Δ heqM
    omega

theorem functionality_typing_extend :
  ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
  Γ ctx
  → Γ ⊢ A type
  → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
      (eqM : x = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
    (Γ_1 ⊢ s ≡ s' ∶ S)
    → (Γ_1 ⊢ s ∶ S)
    → (Γ_1 ⊢ s' ∶ S)
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
  → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : x = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
        (eqM : x = m + 1),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = T
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
  → ∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
    (eqM : x + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
  (Γ_1 ⊢ s ≡ s' ∶ S)
  → (Γ_1 ⊢ s ∶ S)
  → (Γ_1 ⊢ s' ∶ S)
  → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
  → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type:=
  by
    intro n Γ' A hiC hA ihiC ihA m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
    cases heqM
    simp_all
    cases Ξ with
    | start =>
      cases heqΓ
      apply And.right ihA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
    | expand Ξ' A' =>
      cases heqΓ
      cases n with
      | zero =>
        have h1 := gen_ctx_leq Ξ'
        omega
      | succ n' =>
        cases Δ with
        | start =>
          apply And.left ihA
          · apply hssS
          · apply hsS
          · apply hsS'
          rotate_left
          · apply n'
          · apply Ξ'
          · rfl
          · rfl
        | expand Δ' T' =>
          cases m with
          | zero =>
            have h := gen_ctx_neq Δ'
            omega
          | succ m' =>
            apply ihiC
            · apply hssS
            · apply hsS
            · apply hsS'
            rotate_left
            · apply n'
            · apply Ξ'
            · rfl
            · rfl
