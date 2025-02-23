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

theorem functionality_typing_var_eq :
   ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type → Γ ⊢ A type →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
        (eqM : x + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S) →
          (Γ_1 ⊢ s ∶ S) →
            (Γ_1 ⊢ s' ∶ S) →
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ v(0) = t →
                  eqM ▸ v(0) = t →
                    eqM ▸ A⌊↑ₚidₚ⌋ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A hA _ihA m l hleq Γ Δ r r' R u U heqM hrrR hrR hrR' heqΓ hequ hequ' heqU
    cases heqM
    cases hequ
    cases hequ'
    cases heqU
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
        apply hrrR
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
          · apply hrR
      case isFalse hF =>
        simp [substitute_var]
        rw [substitution_conv_zero]
        rw [substitution_shift_substitute_zero]
        split
        case h_1 =>
          cases Δ with
          | start =>
            cases heqΓ
            apply hrrR
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

theorem functionality_typing_weak_eq : ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
   (Γ ⊢ v(i) ≡ v(i) ∶ A) →
     Γ ⊢ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : x = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ v(i) = t →
                     eqM ▸ v(i) = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         Γ ⊢ B type →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
             (eqM : x + 1 = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ v(i)⌊↑ₚidₚ⌋ = t →
                       eqM ▸ v(i)⌊↑ₚidₚ⌋ = t →
                         eqM ▸ A⌊↑ₚidₚ⌋ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' i A B hvvA hB ihvvA ihB m' l' hleq Γ Δ r r' R u U heqM hrrR hrR hrR' heqΓ hequ hequ' heqU
    cases heqM
    cases hequ
    cases hequ'
    cases heqU
    cases n
    case zero =>
      simp [n_substitution]
      simp [substitution_conv_zero]
      simp [substitution_shift_substitute_zero]
      cases Δ with
      | start =>
        simp [expand_ctx]
        cases heqΓ
        apply hvvA
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
          simp [substitute_into_gen_ctx]
          simp [expand_ctx]
          simp [substitution_shift_id_lift]
          apply weakening_term_eq
          · apply ihvvA
            · apply hrrR
            · apply hrR
            · apply hrR'
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
          · apply And.left (And.right substitution)
            apply ihB
            apply hrR
      case isFalse hF =>
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        cases Δ with
        | start =>
          cases heqΓ
          apply hvvA
        | expand Δ' T =>
          have h := gen_ctx_leq Δ'
          omega

theorem functionality_typing_unit_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
  Γ ⬝ 𝟙 ⊢ A type →
    (Γ ⊢ a ∶ A⌈⋆⌉₀) →
      Γ ⬝ 𝟙 ⊢ A type →
        (Γ ⊢ a ∶ A⌈⋆⌉₀) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
            (eqM : n = m + 1),
            (Γ_1 ⊢ s ≡ s' ∶ S) →
              (Γ_1 ⊢ s ∶ S) →
                (Γ_1 ⊢ s' ∶ S) →
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ A.indUnit ⋆ a = t →
                      eqM ▸ a = t → eqM ▸ A⌈⋆⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a hA haA _ihA _ihaA m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'

theorem functionality_typing_pi_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
  (Γ ⬝ A ⊢ b ∶ B) →
    (Γ ⊢ a ∶ A) →
      (Γ ⬝ A ⊢ b ∶ B) →
        (Γ ⊢ a ∶ A) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
            (eqM : n = m + 1),
            (Γ_1 ⊢ s ≡ s' ∶ S) →
              (Γ_1 ⊢ s ∶ S) →
                (Γ_1 ⊢ s' ∶ S) →
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ (λA; b)◃a = t →
                      eqM ▸ b⌈a⌉₀ = t →
                        eqM ▸ B⌈a⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A b B a hbB haA ihbB ihaA m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    sorry

theorem functionality_typing_sigma_comp : ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
 (Γ ⊢ a ∶ A) →
   (Γ ⊢ b ∶ B⌈a⌉₀) →
     (Γ ⬝ ΣA;B) ⊢ C type →
       (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
         (Γ ⊢ a ∶ A) →
           (Γ ⊢ b ∶ B⌈a⌉₀) →
             (Γ ⬝ ΣA;B) ⊢ C type →
               (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
                 ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                   (t T : Tm (m + 1)) (eqM : n = m + 1),
                   (Γ_1 ⊢ s ≡ s' ∶ S) →
                     (Γ_1 ⊢ s ∶ S) →
                       (Γ_1 ⊢ s' ∶ S) →
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ A.indSigma B C c (a&b) = t →
                             eqM ▸ c⌈(ₛidₚ), a, b⌉ = t →
                               eqM ▸ C⌈a&b⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A b B C c haA hbB hC hcC ihaA ihbB ihC ihcC m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    sorry

theorem functionality_typing_iden_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a : Tm n},
 (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
   (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
     (Γ ⊢ a ∶ A) →
       Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
         (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
           (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
             (Γ ⊢ a ∶ A) →
               Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
                 ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                   (t T : Tm (m + 1)) (eqM : n = m + 1),
                   (Γ_1 ⊢ s ≡ s' ∶ S) →
                     (Γ_1 ⊢ s ∶ S) →
                       (Γ_1 ⊢ s' ∶ S) →
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ A.j B b a a (A.refl a) = t →
                             eqM ▸ b = t →
                               eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = T →
                                 Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B b a hB hbB haA hB' ihB ihbB ihaA ihB' m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'

theorem functionality_typing_unit_intro_eq : ∀ {n : Nat} {Γ : Ctx n},
 Γ ctx →
   Γ ctx →
     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
       (eqM : n = m + 1),
       (Γ_1 ⊢ s ≡ s' ∶ S) →
         (Γ_1 ⊢ s ∶ S) →
           (Γ_1 ⊢ s' ∶ S) →
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ ⋆ = t →
                 eqM ▸ ⋆ = t → eqM ▸ 𝟙 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_tt]
    simp [substitution_unit]
    apply IsEqualTerm.unit_intro_eq
    simp_all
    cases Δ
    case start =>
      simp [substitute_into_gen_ctx]
      simp [expand_ctx]
      simp [expand_ctx] at hiC
      exact ctx_decr hiC
    case expand Δ' T =>
      cases m with
      | zero =>
        have h := gen_ctx_leq Δ'
        omega
      | succ m' =>
        apply And.left substitution
        · apply hiC
        · apply hsS
        · omega

theorem functionality_typing_unit_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
 Γ ⬝ 𝟙 ⊢ A ≡ A' type →
   (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀) →
     (Γ ⊢ b ≡ b' ∶ 𝟙) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
           (eqM : n + 1 = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A = T → eqM ▸ A' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ a = t →
                       eqM ▸ a' = t →
                         eqM ▸ A⌈⋆⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
               (eqM : n = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ b = t →
                         eqM ▸ b' = t →
                           eqM ▸ 𝟙 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
               (eqM : n = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ A.indUnit b a = t →
                         eqM ▸ A'.indUnit b' a' = t →
                           eqM ▸ A⌈b⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply IsEqualTerm.unit_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution]
      rw [←substitution_unit]
      rw [extend_expand_context_n_substitution]
      apply ihAA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_tt]
      rw [←substitution_zero_lift]
      apply ihaaA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · rw [←substitution_unit]
      apply ihbb1
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_empty_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
 Γ ⬝ 𝟘 ⊢ A ≡ A' type →
   (Γ ⊢ b ≡ b' ∶ 𝟘) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : n + 1 = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ A = T → eqM ▸ A' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = t →
                     eqM ▸ b' = t → eqM ▸ 𝟘 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A.indEmpty b = t →
                     eqM ▸ A'.indEmpty b' = t →
                       eqM ▸ A⌈b⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' b b' hAA hbb0 ihAA ihbb0 m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply IsEqualTerm.empty_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution]
      rw [←substitution_empty]
      rw [extend_expand_context_n_substitution]
      apply ihAA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · rw [←substitution_empty]
      apply ihbb0
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_pi_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) →
      Γ ⊢ A ≡ A' type →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
            (eqM : n + 1 = m + 1),
            (Γ_1 ⊢ s ≡ s' ∶ S) →
              (Γ_1 ⊢ s ∶ S) →
                (Γ_1 ⊢ s' ∶ S) →
                  eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ b = t →
                      eqM ▸ b' = t → eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A = T → eqM ▸ A' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      (eqM ▸ λA; b) = t →
                        (eqM ▸ λA'; b') = t →
                          (eqM ▸ ΠA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉
 :=
  by
    intro n Γ A A' b b' B hbbB hPiPi ihbbB ihPiPi m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    rw [←heqt]
    rw [←heqT]
    simp [substitute]
    apply IsEqualTerm.pi_intro_eq
    · simp [lift_subst_n]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      cases heqt
      cases heqt'
      apply ihbbB
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · cases heqt
      cases heqt'
      apply ihPiPi
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_pi_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
 (Γ ⊢ f ≡ f' ∶ ΠA;B) →
   (Γ ⊢ a ≡ a' ∶ A) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ f = t →
                   eqM ▸ f' = t →
                     (eqM ▸ ΠA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a = t →
                     eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ f◃a = t →
                     eqM ▸ f'◃a' = t →
                       eqM ▸ B⌈a⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' f f' A B a a' hffPi haaA ihffPi ihaaA m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.pi_elim_eq
    · rw [←substitution_pi]
      apply ihffPi
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · apply ihaaA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_sigma_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
 (Γ ⊢ a ≡ a' ∶ A) →
   (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = t →
                   eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = t →
                     eqM ▸ b' = t →
                       eqM ▸ B⌈a⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a&b = t →
                     eqM ▸ a'&b' = t →
                       (eqM ▸ ΣA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a a' A b b' B haaA hbbB ihaaA ihbbB m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaaA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      simp [←substitution_zero_lift]
      apply ihbbB
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_sigma_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
 {c c' : Tm (n + 1 + 1)},
 Γ ⊢ ΣA;B ≡ ΣA';B' type →
   (Γ ⊢ p ≡ p' ∶ ΣA;B) →
     (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
       (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     (eqM ▸ ΣA;B) = T →
                       (eqM ▸ ΣA';B') = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
               (eqM : n = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ p = t →
                         eqM ▸ p' = t →
                           (eqM ▸ ΣA;B) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
                 (eqM : n + 1 = m + 1),
                 (Γ_1 ⊢ s ≡ s' ∶ S) →
                   (Γ_1 ⊢ s ∶ S) →
                     (Γ_1 ⊢ s' ∶ S) →
                       (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                         eqM ▸ C = T → eqM ▸ C' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                   (t T : Tm (m + 1)) (eqM : n + 1 + 1 = m + 1),
                   (Γ_1 ⊢ s ≡ s' ∶ S) →
                     (Γ_1 ⊢ s ∶ S) →
                       (Γ_1 ⊢ s' ∶ S) →
                         eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ c = t →
                             eqM ▸ c' = t →
                               eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = T →
                                 Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
                 ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                   (t T : Tm (m + 1)) (eqM : n = m + 1),
                   (Γ_1 ⊢ s ≡ s' ∶ S) →
                     (Γ_1 ⊢ s ∶ S) →
                       (Γ_1 ⊢ s' ∶ S) →
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ A.indSigma B C c p = t →
                             eqM ▸ A'.indSigma B' C' c' p' = t →
                               eqM ▸ C⌈p⌉₀ = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B A' B' p p' C C' c c' hSiSi hppSi hCC hccC ihSiSi ihppSi ihCC ihccC
    intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.sigma_elim_eq
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [←substitution_sigma]
      apply ihSiSi
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      apply ihppSi
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihCC
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [subst_subst_sigma_C]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihccC
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_iden_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
 Γ ⊢ A ≡ A' type →
   (Γ ⊢ a ≡ a' ∶ A) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ A = T → eqM ▸ A' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a = t →
                     eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A.refl a = t →
                     eqM ▸ A'.refl a' = t →
                       (eqM ▸ a ≃[A] a) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' a a' hAA haaA ihAA ihaaA m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.iden_intro_eq
    · apply ihAA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · apply ihaaA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem funcitonality_typing_iden_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' a₁ a₃ A' a₂ a₄ p p' : Tm n},
 (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type →
   (Γ ⊢ b ≡ b' ∶ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉) →
     Γ ⊢ a₁ ≃[A] a₃ ≡ a₂ ≃[A'] a₄ type →
       (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃) →
         Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ type →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
               (eqM : n + 1 + 1 + 1 = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ B = T → eqM ▸ B' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                 (eqM : n = m + 1),
                 (Γ_1 ⊢ s ≡ s' ∶ S) →
                   (Γ_1 ⊢ s ∶ S) →
                     (Γ_1 ⊢ s' ∶ S) →
                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                         eqM ▸ b = t →
                           eqM ▸ b' = t →
                             eqM ▸ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉ = T →
                               Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
                   (eqM : n = m + 1),
                   (Γ_1 ⊢ s ≡ s' ∶ S) →
                     (Γ_1 ⊢ s ∶ S) →
                       (Γ_1 ⊢ s' ∶ S) →
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           (eqM ▸ a₁ ≃[A] a₃) = T →
                             (eqM ▸ a₂ ≃[A'] a₄) = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
                 (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                     (t T : Tm (m + 1)) (eqM : n = m + 1),
                     (Γ_1 ⊢ s ≡ s' ∶ S) →
                       (Γ_1 ⊢ s ∶ S) →
                         (Γ_1 ⊢ s' ∶ S) →
                           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                             eqM ▸ p = t →
                               eqM ▸ p' = t →
                                 (eqM ▸ a₁ ≃[A] a₃) = T →
                                   Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
                   Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ type →
                     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
                       (t T : Tm (m + 1)) (eqM : n = m + 1),
                       (Γ_1 ⊢ s ≡ s' ∶ S) →
                         (Γ_1 ⊢ s ∶ S) →
                           (Γ_1 ⊢ s' ∶ S) →
                             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                               eqM ▸ A.j B b a₁ a₃ p = t →
                                 eqM ▸ A'.j B' b' a₂ a₄ p' = t →
                                   eqM ▸ B⌈(ₛidₚ), a₁, a₃, p⌉ = T →
                                     Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hIdId hppId hB' ihBB ihbbB ihIdId ihppId ihB'
    intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
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
      apply ihBB
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
    · rw [←substitution_refl]
      rw [←subst_subst_iden_elim]
      apply ihbbB
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · rw [←substitution_iden]
      rw [←substitution_iden]
      apply ihIdId
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
    · rw [←substitution_iden]
      apply ihppId
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · rw [←subst_subst_iden_elim]
      apply And.left (And.right substitution)
      · apply ihB'
      · apply hsS

theorem functionality_typing_univ_unit_eq :
 ∀ {n : Nat} {Γ : Ctx n},
 Γ ctx →
   Γ ctx →
     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
       (eqM : n = m + 1),
       (Γ_1 ⊢ s ≡ s' ∶ S) →
         (Γ_1 ⊢ s ∶ S) →
           (Γ_1 ⊢ s' ∶ S) →
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ 𝟙 = t →
                 eqM ▸ 𝟙 = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_univ]
    simp [substitution_unit]
    apply IsEqualTerm.univ_unit_eq
    apply And.left substitution
    · apply hiC
    · apply hsS
    omega

theorem functionality_typing_univ_empty_eq : ∀ {n : Nat} {Γ : Ctx n},
 Γ ctx →
   Γ ctx →
     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
       (eqM : n = m + 1),
       (Γ_1 ⊢ s ≡ s' ∶ S) →
         (Γ_1 ⊢ s ∶ S) →
           (Γ_1 ⊢ s' ∶ S) →
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ 𝟘 = t →
                 eqM ▸ 𝟘 = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_univ]
    simp [substitution_empty]
    apply IsEqualTerm.univ_empty_eq
    apply And.left substitution
    · apply hiC
    · apply hsS
    omega

theorem functionality_typing_univ_pi_eq :
 ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
 (Γ ⊢ A ≡ A' ∶ 𝒰) →
   (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ A = t →
                   eqM ▸ A' = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n + 1 = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ B = t →
                     eqM ▸ B' = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   (eqM ▸ ΠA;B) = t →
                     (eqM ▸ ΠA';B') = t →
                       eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_pi_eq
    · rw [←substitution_univ]
      apply ihAAU
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [←substitution_univ]
      apply ihBBU
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_univ_sigma_eq :
 ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
 (Γ ⊢ A ≡ A' ∶ 𝒰) →
   (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ A = t →
                   eqM ▸ A' = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n + 1 = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ B = t →
                     eqM ▸ B' = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   (eqM ▸ ΣA;B) = t →
                     (eqM ▸ ΣA';B') = t →
                       eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_sigma_eq
    · rw [←substitution_univ]
      apply ihAAU
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [←substitution_univ]
      apply ihBBU
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_univ_iden_eq :
 ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
 (Γ ⊢ A ≡ A' ∶ 𝒰) →
   (Γ ⊢ a₁ ≡ a₂ ∶ A) →
     (Γ ⊢ a₃ ≡ a₄ ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A = t →
                     eqM ▸ A' = t → eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
             (eqM : n = m + 1),
             (Γ_1 ⊢ s ≡ s' ∶ S) →
               (Γ_1 ⊢ s ∶ S) →
                 (Γ_1 ⊢ s' ∶ S) →
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ a₁ = t →
                       eqM ▸ a₂ = t →
                         eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
               (eqM : n = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ a₃ = t →
                         eqM ▸ a₄ = t →
                           eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
               (eqM : n = m + 1),
               (Γ_1 ⊢ s ≡ s' ∶ S) →
                 (Γ_1 ⊢ s ∶ S) →
                   (Γ_1 ⊢ s' ∶ S) →
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       (eqM ▸ a₁ ≃[A] a₃) = t →
                         (eqM ▸ a₂ ≃[A'] a₄) = t →
                           eqM ▸ 𝒰 = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_iden_eq
    · rw [←substitution_univ]
      apply ihAAU
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · apply ihaaA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · apply ihaaA'
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl

theorem functionality_typing_ty_conv_eq :
 ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
 (Γ ⊢ a ≡ b ∶ A) →
   Γ ⊢ A ≡ B type →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = t →
                   eqM ▸ b = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A = T → eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a = t →
                     eqM ▸ b = t → eqM ▸ B = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a b A B habA hAB ihabA ihAB m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.ty_conv_eq
    · apply ihabA
      · apply hssS
      · apply hsS
      · apply hsS'
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · apply And.left (And.right (And.right (And.right substitution)))
      · apply hAB
      · apply hsS

theorem functionality_typing_term_symm : ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
 (Γ ⊢ a ≡ a' ∶ A) →
   (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
       (eqM : n = m + 1),
       (Γ_1 ⊢ s ≡ s' ∶ S) →
         (Γ_1 ⊢ s ∶ S) →
           (Γ_1 ⊢ s' ∶ S) →
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = t →
                 eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) →
     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
       (eqM : n = m + 1),
       (Γ_1 ⊢ s ≡ s' ∶ S) →
         (Γ_1 ⊢ s ∶ S) →
           (Γ_1 ⊢ s' ∶ S) →
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a' = t →
                 eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a a' A haaA ihaaA m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply ihaaA
    · apply hssS
    · apply hsS
    · apply hsS'
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem functionality_typing_term_trans :
 ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
 (Γ ⊢ a ≡ b ∶ T) →
   (Γ ⊢ b ≡ c ∶ T) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T_1 : Tm (m + 1))
         (eqM : n = m + 1),
         (Γ_1 ⊢ s ≡ s' ∶ S) →
           (Γ_1 ⊢ s ∶ S) →
             (Γ_1 ⊢ s' ∶ S) →
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = t →
                   eqM ▸ b = t → eqM ▸ T = T_1 → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T_1⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T_1 : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = t →
                     eqM ▸ c = t →
                       eqM ▸ T = T_1 → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T_1⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T_1 : Tm (m + 1))
           (eqM : n = m + 1),
           (Γ_1 ⊢ s ≡ s' ∶ S) →
             (Γ_1 ⊢ s ∶ S) →
               (Γ_1 ⊢ s' ∶ S) →
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a = t →
                     eqM ▸ c = t → eqM ▸ T = T_1 → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' T a b c habT hbcT ihabT ihbcT m l hleq Γ Δ s s' S u U heqM hssS hsS hsS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply ihabT
    · apply hssS
    · apply hsS
    · apply hsS'
    · rfl
    · rfl
    · sorry
    · rfl
    · rfl
