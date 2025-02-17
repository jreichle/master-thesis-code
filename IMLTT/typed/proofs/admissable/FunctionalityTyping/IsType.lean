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
import IMLTT.typed.proofs.admissable.SubstitutionGeneral

theorem functionality_typing_unit_form : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     Γ ctx →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟙 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsEqualType.unit_form_eq
    simp_all
    cases Δ
    case start =>
      simp [substitute_into_gen_ctx]
      simp [expand_ctx]
      simp [expand_ctx] at ihiC
      exact ctx_decr ihiC
    case expand Δ' T =>
      cases m with
      | zero =>
        have h := gen_ctx_leq Δ'
        omega
      | succ m' =>
        apply And.left substitution
        · apply ihiC
        · apply hsS
        · omega

theorem functionality_typing_empty_form : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     Γ ctx →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟘 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsEqualType.empty_form_eq
    simp_all
    cases Δ
    case start =>
      simp [substitute_into_gen_ctx]
      simp [expand_ctx]
      simp [expand_ctx] at ihiC
      exact ctx_decr ihiC
    case expand Δ' T =>
      cases m with
      | zero =>
        have h := gen_ctx_leq Δ'
        omega
      | succ m' =>
        apply And.left substitution
        · apply ihiC
        · apply hsS
        · omega

theorem functionality_typing_pi_form : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
   Γ ⊢ A type →
     Γ ⬝ A ⊢ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
             (eqM : n + 1 = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΠA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type :=
  by
    intro n Γ' A B hA hB ihA ihB m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsEqualType.pi_form_eq
    · apply ihA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihB
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl

theorem functionality_typing_sigma_form : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
   Γ ⊢ A type →
     Γ ⬝ A ⊢ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
             (eqM : n + 1 = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΣA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type :=
  by
    intro n Γ' A B hA hB ihA ihB m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsEqualType.sigma_form_eq
    · apply ihA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihB
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl

theorem functionality_typing_iden_form : ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
    (Γ ⊢ a ∶ A) →
      (Γ ⊢ a' ∶ A) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
            (eqM : n = m + 1),
            (Γ_1 ⊢ s ≡ s' ∶ S) →
              (Γ_1 ⊢ s ∶ S) →
                (Γ_1 ⊢ s' ∶ S) →
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      (eqM ▸ a ≃[A] a') = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type  :=
  by
    intro n Γ' a A a' haA haA' ihaA ihaA' m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsEqualType.iden_form_eq
    · sorry
    · apply ihaA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · sorry
      -- apply ihaA' -- need ty_conv
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry

theorem functionality_typing_univ_form : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     Γ ctx →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsEqualType.univ_form_eq
    simp_all
    cases Δ
    case start =>
      simp [substitute_into_gen_ctx]
      simp [expand_ctx]
      simp [expand_ctx] at ihiC
      exact ctx_decr ihiC
    case expand Δ' T =>
      cases m with
      | zero =>
        have h := gen_ctx_leq Δ'
        omega
      | succ m' =>
        apply And.left substitution
        · apply ihiC
        · apply hsS
        · omega

theorem functionality_typing_univ_elim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
   (Γ ⊢ A ∶ 𝒰) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t t' T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ A = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t'⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type :=
  by
    intro n Γ' A hAU ihAU  m l hleq Γ Δ s s' S T heqM hssS hsS hsS' heqΓ heqT
    cases heqM
    cases heqΓ
    cases heqT
    apply IsEqualType.univ_elim_eq
    rw [←substitution_univ]
    apply ihAU
    · apply hssS
    · apply hsS
    · apply hsS'
    · rfl
    · rfl
    · rfl
    · rfl
