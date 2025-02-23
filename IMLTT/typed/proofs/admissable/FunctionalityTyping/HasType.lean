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
import IMLTT.typed.proofs.admissable.Substitution

theorem functionality_typing_var : ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
   Γ ⊢ A type →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : x = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : x + 1 = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ v(0) = t → eqM ▸ A⌊↑ₚidₚ⌋ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
    cases heqM
    cases heqt
    cases heqT
    cases n with
    | zero =>
      simp [substitute]
      simp [n_substitution]
      simp [substitute_var]
      rw [substitution_conv_zero]
      rw [substitution_shift_substitute_zero]
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_into_gen_ctx]
        simp [expand_ctx]
        apply hssS
      | expand Δ' T =>
        have h1 := gen_ctx_leq Δ'
        omega
    | succ n' =>
      simp [substitute]
      simp [n_substitution]
      split
      case isTrue hT =>
        simp [substitute_var]
        simp [substitution_shift_id_lift]
        cases Δ with
        | start =>
          omega
        | expand Δ' T =>
          rw [←extend_expand_context] at heqΓ
          cases heqΓ
          apply IsEqualTerm.var_eq
          apply And.left (And.right substitution)
          · apply hA
          · apply hsS
      case isFalse hF =>
        simp [substitute_var]
        rw [substitution_conv_zero]
        rw [substitution_shift_substitute_zero]
        split
        case h_1 =>
          cases Δ with
          | start =>
            cases heqΓ
            apply hssS
          | expand Δ' T =>
            have h1 := gen_ctx_leq Δ'
            omega
        case h_2 h =>
          cases Δ with
          | start =>
            cases heqΓ
            simp [expand_ctx]
            simp [weakening_id]
            cases h
          | expand Δ' T =>
            have h1 := gen_ctx_leq Δ'
            omega

theorem functionality_typing_weak : ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
   (Γ ⊢ v(i) ∶ A) →
     Γ ⊢ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : x = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ v(i) = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
             (eqM : x = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
             (eqM : x + 1 = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ v(i)⌊↑ₚidₚ⌋ = t →
                       eqM ▸ A⌊↑ₚidₚ⌋ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n x Γ A B hvA hB ihvA ihB m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
    cases heqM
    cases heqt
    cases heqT
    simp_all
    cases n
    case zero =>
      simp [n_substitution]
      simp [substitution_conv_zero]
      simp [substitution_shift_substitute_zero]
      cases Δ with
      | start =>
        simp [expand_ctx]
        cases heqΓ
        apply defeq_refl_term hvA
      | expand Δ' T =>
        have h := gen_ctx_neq Δ'
        omega
    case succ n' =>
      simp [n_substitution]
      split
      case isTrue hT =>
        simp [substitution_shift_id_lift]
        cases Δ with
        | start =>
          omega
        | expand Δ' T =>
          cases heqΓ
          have h := gen_ctx_leq Δ'
          simp_all
          simp [substitute_into_gen_ctx]
          simp [expand_ctx]
          apply weakening_term_eq
          · apply ihvA
            · apply hssS
            · apply hsS
            · apply hsS'
            · rfl
            · rfl
            · rfl
            · rfl
          · apply And.left (And.right substitution)
            · apply hB
            · apply hsS
      case isFalse hF =>
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        cases Δ with
        | start =>
          cases heqΓ
          apply defeq_refl_term hvA
        | expand Δ' T =>
          have h := gen_ctx_leq Δ'
          omega

theorem functionality_typing_unit_intro : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     Γ ctx →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ ⋆ = t → eqM ▸ 𝟙 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitution_tt]
    simp [substitution_unit]
    apply IsEqualTerm.unit_intro_eq
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

theorem functionality_typing_pi_intro : 
 ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
   (Γ ⬝ A ⊢ b ∶ B) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n + 1 = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ b = t → eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 (eqM ▸ λA; b) = t → (eqM ▸ ΠA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
 :=
  by
    intro n Γ' A b B hbB ihbB
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp [substitute]
      apply IsEqualTerm.pi_intro_eq
      · simp [lift_subst_n]
        rw [lift_n_substitution]
        rw [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply ihbB
        · apply hssS
        · apply hsS
        · apply hsS'
        · rfl
        · rfl
        · rfl
        · rfl
      · sorry
      -- simp [lift_subst_n]
      -- rw [←substitution_pi]
      -- rw [←substitution_pi]
      -- any_goals sorry

theorem functionality_typing_sigma_intro :
 ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
   (Γ ⊢ a ∶ A) →
     (Γ ⊢ b ∶ B⌈a⌉₀) →
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
                     eqM ▸ b = t → eqM ▸ B⌈a⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ a&b = t → (eqM ▸ ΣA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A b B haA hbB ihaA ihbB m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaA
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl
    · simp [lift_subst_n]
      simp [←substitution_zero_lift]
      apply ihbB
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl

-- case HasTypeIdenIntro
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
--     (Γ ⊢ a ∶ A) →
--       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--           (eqM : n = m + 1),
--           (Γ_1 ⊢ s ≡ s' ∶ S) →
--             (Γ_1 ⊢ s ∶ S) →
--               (Γ_1 ⊢ s' ∶ S) →
--                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                   eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--           (eqM : n = m + 1),
--           (Γ_1 ⊢ s ≡ s' ∶ S) →
--             (Γ_1 ⊢ s ∶ S) →
--               (Γ_1 ⊢ s' ∶ S) →
--                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                   eqM ▸ A.refl a = t →
--                     (eqM ▸ a ≃[A] a) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeUnivUnit
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--     Γ ctx →
--       Γ ctx →
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--           (eqM : n = m + 1),
--           (Γ_1 ⊢ s ≡ s' ∶ S) →
--             (Γ_1 ⊢ s ∶ S) →
--               (Γ_1 ⊢ s' ∶ S) →
--                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                   eqM ▸ 𝟙 = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeUnivEmpty
-- ⊢ ∀ {n : Nat} {Γ : Ctx n},
--     Γ ctx →
--       Γ ctx →
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--           (eqM : n = m + 1),
--           (Γ_1 ⊢ s ≡ s' ∶ S) →
--             (Γ_1 ⊢ s ∶ S) →
--               (Γ_1 ⊢ s' ∶ S) →
--                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                   eqM ▸ 𝟘 = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeUnivPi
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--     (Γ ⊢ A ∶ 𝒰) →
--       (Γ ⬝ A ⊢ B ∶ 𝒰) →
--         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--             (eqM : n = m + 1),
--             (Γ_1 ⊢ s ≡ s' ∶ S) →
--               (Γ_1 ⊢ s ∶ S) →
--                 (Γ_1 ⊢ s' ∶ S) →
--                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                     eqM ▸ A = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n + 1 = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ B = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       (eqM ▸ ΠA;B) = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeUnivSigma
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
--     (Γ ⊢ A ∶ 𝒰) →
--       (Γ ⬝ A ⊢ B ∶ 𝒰) →
--         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--             (eqM : n = m + 1),
--             (Γ_1 ⊢ s ≡ s' ∶ S) →
--               (Γ_1 ⊢ s ∶ S) →
--                 (Γ_1 ⊢ s' ∶ S) →
--                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                     eqM ▸ A = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n + 1 = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ B = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       (eqM ▸ ΣA;B) = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeUnivIden
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
--     (Γ ⊢ A ∶ 𝒰) →
--       (Γ ⊢ a ∶ A) →
--         (Γ ⊢ a' ∶ A) →
--           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ A = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                 (eqM : n = m + 1),
--                 (Γ_1 ⊢ s ≡ s' ∶ S) →
--                   (Γ_1 ⊢ s ∶ S) →
--                     (Γ_1 ⊢ s' ∶ S) →
--                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                         eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                   (eqM : n = m + 1),
--                   (Γ_1 ⊢ s ≡ s' ∶ S) →
--                     (Γ_1 ⊢ s ∶ S) →
--                       (Γ_1 ⊢ s' ∶ S) →
--                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                           eqM ▸ a' = t →
--                             eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--                 ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                   (eqM : n = m + 1),
--                   (Γ_1 ⊢ s ≡ s' ∶ S) →
--                     (Γ_1 ⊢ s ∶ S) →
--                       (Γ_1 ⊢ s' ∶ S) →
--                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                           (eqM ▸ a ≃[A] a') = t →
--                             eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeUnitElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
--     Γ ⬝ 𝟙 ⊢ A type →
--       (Γ ⊢ a ∶ A⌈⋆⌉₀) →
--         (Γ ⊢ b ∶ 𝟙) →
--           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
--               (eqM : n + 1 = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
--             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                 (eqM : n = m + 1),
--                 (Γ_1 ⊢ s ≡ s' ∶ S) →
--                   (Γ_1 ⊢ s ∶ S) →
--                     (Γ_1 ⊢ s' ∶ S) →
--                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                         eqM ▸ a = t →
--                           eqM ▸ A⌈⋆⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                   (eqM : n = m + 1),
--                   (Γ_1 ⊢ s ≡ s' ∶ S) →
--                     (Γ_1 ⊢ s ∶ S) →
--                       (Γ_1 ⊢ s' ∶ S) →
--                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                           eqM ▸ b = t → eqM ▸ 𝟙 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--                 ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                   (eqM : n = m + 1),
--                   (Γ_1 ⊢ s ≡ s' ∶ S) →
--                     (Γ_1 ⊢ s ∶ S) →
--                       (Γ_1 ⊢ s' ∶ S) →
--                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                           eqM ▸ A.indUnit b a = t →
--                             eqM ▸ A⌈b⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypeEmptyElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
--     Γ ⬝ 𝟘 ⊢ A type →
--       (Γ ⊢ b ∶ 𝟘) →
--         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
--             (eqM : n + 1 = m + 1),
--             (Γ_1 ⊢ s ≡ s' ∶ S) →
--               (Γ_1 ⊢ s ∶ S) →
--                 (Γ_1 ⊢ s' ∶ S) →
--                   eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
--           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ b = t → eqM ▸ 𝟘 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ A.indEmpty b = t →
--                         eqM ▸ A⌈b⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
-- case HasTypePiElim
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
--     (Γ ⊢ f ∶ ΠA;B) →
--       (Γ ⊢ a ∶ A) →
--         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--             (eqM : n = m + 1),
--             (Γ_1 ⊢ s ≡ s' ∶ S) →
--               (Γ_1 ⊢ s ∶ S) →
--                 (Γ_1 ⊢ s' ∶ S) →
--                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                     eqM ▸ f = t → (eqM ▸ ΠA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ f◃a = t → eqM ▸ B⌈a⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉


theorem functionality_typing_sigma_elim :
 ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
   (Γ ⊢ p ∶ ΣA;B) →
     (Γ ⬝ ΣA;B) ⊢ C type →
       (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ p = t →
                       (eqM ▸ ΣA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
               (eqM : n + 1 = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ C = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                 (eqM : n + 1 + 1 = m + 1),
                 (Γ_1 ⊢ s ≡ s' ∶ S) →
                   (Γ_1 ⊢ s ∶ S) →
                     (Γ_1 ⊢ s' ∶ S) →
                       eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                         eqM ▸ c = t →
                           eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = T →
                             Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                 (eqM : n = m + 1),
                 (Γ_1 ⊢ s ≡ s' ∶ S) →
                   (Γ_1 ⊢ s ∶ S) →
                     (Γ_1 ⊢ s' ∶ S) →
                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                         eqM ▸ A.indSigma B C c p = t →
                           eqM ▸ C⌈p⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B p C c hpSi hC hcC ihpSi ihC ihcC m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.sigma_elim_eq
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [←substitution_sigma]
      sorry
      -- apply ihSiSi
      -- · rfl
      -- · rfl
      -- · rfl
      -- · apply hsS
      -- · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      apply ihpSi
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihC
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl
    · simp [lift_subst_n]
      rw [subst_subst_sigma_C]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihcC
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl

theorem functionality_typing_iden_elim :
 ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a a' p : Tm n},
   (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
     (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
       (Γ ⊢ p ∶ a ≃[A] a') →
         Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
               (eqM : n + 1 + 1 + 1 = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                 (eqM : n = m + 1),
                 (Γ_1 ⊢ s ≡ s' ∶ S) →
                   (Γ_1 ⊢ s ∶ S) →
                     (Γ_1 ⊢ s' ∶ S) →
                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                         eqM ▸ b = t →
                           eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = T →
                             Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                   (eqM : n = m + 1),
                   (Γ_1 ⊢ s ≡ s' ∶ S) →
                     (Γ_1 ⊢ s ∶ S) →
                       (Γ_1 ⊢ s' ∶ S) →
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ p = t →
                             (eqM ▸ a ≃[A] a') = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
                 (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
                     (eqM : n = m + 1),
                     (Γ_1 ⊢ s ≡ s' ∶ S) →
                       (Γ_1 ⊢ s ∶ S) →
                         (Γ_1 ⊢ s' ∶ S) →
                           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                             eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = T →
                               Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
                   ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                     (t T : Tm (m + 1)) (eqM : n = m + 1),
                     (Γ_1 ⊢ s ≡ s' ∶ S) →
                       (Γ_1 ⊢ s ∶ S) →
                         (Γ_1 ⊢ s' ∶ S) →
                           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                             eqM ▸ A.j B b a a' p = t →
                               eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = T →
                                 Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B b a a' p hB hbB hpId hB' ihB ihbB ihpId ihB' m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    rw [subst_subst_iden_elim]
    apply IsEqualTerm.iden_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution]
      simp [←substitution_shift_id_lift]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      simp_all
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihB
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl
    · rw [←substitution_refl]
      rw [←subst_subst_iden_elim]
      apply ihbB
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl
    · rw [←substitution_iden]
      rw [←substitution_iden]
      sorry
      -- apply ihIdId
      -- · rfl
      -- · rfl
      -- · rfl
      -- · apply hsS
      -- · rfl
    · rw [←substitution_iden]
      apply ihpId
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl
    · rw [←subst_subst_iden_elim]
      apply And.left (And.right substitution)
      rotate_left
      · apply hsS
      · apply hB'

-- case HasTypeTyConv
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
--     (Γ ⊢ a ∶ A) →
--       Γ ⊢ A ≡ B type →
--         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--             (eqM : n = m + 1),
--             (Γ_1 ⊢ s ≡ s' ∶ S) →
--               (Γ_1 ⊢ s ∶ S) →
--                 (Γ_1 ⊢ s' ∶ S) →
--                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                     eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
--           Γ ⊢ A ≡ B type →
--             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ a = t → eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
