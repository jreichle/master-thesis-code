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

import IMLTT.typed.proofs.admissable.FunctionalityTyping.IsCtx
import IMLTT.typed.proofs.admissable.FunctionalityTyping.IsType
import IMLTT.typed.proofs.admissable.FunctionalityTyping.HasType

set_option pp.proofs true

theorem functionality_typing :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {T : Tm (n + 1)} {s s' S : Tm l},
      (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
      → (Γ ⬝ S ⊗ Δ ⊢ T type)
      → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) ≡ (T⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) type
    ) ∧
    (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {t T : Tm (n + 1)} {s s' S : Tm l},
      (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
      → (Γ ⬝ S ⊗ Δ ⊢ t ∶ T)
      → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢
        (t⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) ≡ (t⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) 
        ∶ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉)
    ) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A)) :=
  by
    suffices h :
  (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        ∀ (m l : Nat) (k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
          (Γ_1 ⊢ s ≡ s' ∶ S) →
            (Γ_1 ⊢ s ∶ S) →
              (Γ_1 ⊢ s' ∶ S) →
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
              (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
                (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
                (Γ_1 ⊢ s ≡ s' ∶ S) →
                  (Γ_1 ⊢ s ∶ S) →
                    (Γ_1 ⊢ s' ∶ S) →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                (eqM : n = m + 1),
                (Γ_1 ⊢ s ≡ s' ∶ S) →
                  (Γ_1 ⊢ s ∶ S) →
                    (Γ_1 ⊢ s' ∶ S) →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → False → True) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → False → True
    by
      any_goals repeat' (apply And.intro)
      · intro n Γ hiC
        apply hiC
      · intro n l Γ Δ T s s' S hssS hsS hsS' hT
        have h1 := (And.left (And.right h)) hT
        apply And.right h1
        · apply hssS
        · apply hsS
        · apply hsS'
        · rfl
        · rfl
        · rfl
      · intro n l Γ Δ t T s s' S hssS hsS hsS' htT
        have h1 := (And.left (And.right (And.right h))) htT
        apply And.right h1
        · apply hssS
        · apply hsS
        · apply hsS'
        · rfl
        · rfl
        · rfl
        · rfl
      · intro n Γ A A' hAA
        apply hAA
      · intro n Γ A a a' haaA
        apply haaA
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        (∀m l k {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) s s' S T,
          (Γ ⊢ s ≡ s' ∶ S)
          → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
          → eqM ▸ Γ' = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ →
          (Γ ⊗ ⌈s⌉(Δ w/(Nat.le_refl l)) ⊢ T⌈s/ₙ (leq)⌉ ≡ T⌈s'/ₙ (leq)⌉ type)))
      (motive_2 := fun {n} Γ' A' _hA =>
        (∀m l k {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) s s' S T,
          (Γ ⊢ s ≡ s' ∶ S)
          → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
          → eqM ▸ Γ' = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ →
          (Γ ⊗ ⌈s⌉(Δ w/(Nat.le_refl l)) ⊢ T⌈s/ₙ (leq)⌉ ≡ T⌈s'/ₙ (leq)⌉ type))
        ∧
        ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T⌈s'/ₙ leq⌉) type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        (∀m l k {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) s s' S T,
          (Γ ⊢ s ≡ s' ∶ S)
          → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
          → eqM ▸ Γ' = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ →
          (Γ ⊗ ⌈s⌉(Δ w/(Nat.le_refl l)) ⊢ T⌈s/ₙ (leq)⌉ ≡ T⌈s'/ₙ (leq)⌉ type))
        ∧
        (∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = t → eqM ▸ A' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉)))
      (motive_4 := fun {n} Γ' C C' _hCC => False → True)
      (motive_5 := fun {n} Γ' c c' C _haaA => False → True)
    case IsCtxEmpty =>
       apply functionality_typing_empty
    case IsCtxExtend =>
      apply functionality_typing_extend
    case IsTypeUnitForm =>
      apply functionality_typing_unit_form
    case IsTypeEmptyForm =>
      apply functionality_typing_empty_form
    case IsTypePiForm =>
      apply functionality_typing_pi_form
    case IsTypeSigmaForm =>
      apply functionality_typing_sigma_form
    case IsTypeIdenForm =>
      apply functionality_typing_iden_form
    case IsTypeUnivForm =>
      apply functionality_typing_univ_form
    case IsTypeUnivElim =>
      apply functionality_typing_univ_elim
    case HasTypeVar =>
      apply functionality_typing_var
    case HasTypeWeak =>
      apply functionality_typing_weak
    case HasTypeUnitIntro =>
      apply functionality_typing_unit_intro
    case HasTypePiIntro =>
      apply functionality_typing_pi_intro
    case HasTypeSigmaIntro =>
      apply functionality_typing_sigma_intro
    case HasTypeIdenIntro =>
      apply functionality_typing_iden_intro
    case HasTypeUnivUnit =>
      apply functionality_typing_univ_unit
    case HasTypeUnivEmpty =>
      apply functionality_typing_univ_empty
    case HasTypeUnivPi =>
      apply functionality_typing_univ_pi
    case HasTypeUnivSigma =>
      apply functionality_typing_univ_sigma
    case HasTypeUnivIden =>
      apply functionality_typing_univ_iden
    case HasTypeUnitElim =>
      apply functionality_typing_unit_elim
    case HasTypeEmptyElim =>
      apply functionality_typing_empty_elim
    case HasTypePiElim =>
      apply functionality_typing_pi_elim
    case HasTypeSigmaFirst =>
      apply functionality_typing_sigma_first
    case HasTypeSigmaSecond =>
      apply functionality_typing_sigma_second
    case HasTypeIdenElim =>
      apply functionality_typing_iden_elim
    case HasTypeTyConv =>
      apply functionality_typing_ty_conv
    any_goals sorry
    --   repeat'
    --   first
    --   | intro a
    --   | apply False.elim
    --   | assumption

  theorem functionality_typing_type {l : Nat} {Γ : Ctx l} {s s' S : Tm l} {T : Tm (l + 1)} :
      Γ ⬝ S ⊢ T type
      → (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
      → (Γ ⊢ T⌈s⌉₀ ≡ T⌈s'⌉₀ type) :=
  by
    intro hT hssS hsS hsS'
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right functionality_typing)
    · apply hssS
    · apply hsS
    · apply hsS'
    · apply hT

theorem functionality_typing_term {l : Nat} {Γ : Ctx l} {s s' S : Tm l} {t T : Tm (l + 1)} :
      (Γ ⬝ S ⊢ t ∶ T)
      → (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
      → (Γ ⊢  t⌈s⌉₀ ≡ t⌈s'⌉₀ ∶ T⌈s⌉₀) :=
  by
    intro htT hssS hsS hsS'
    simp [substitute_zero]
    simp [zero_substitution_conv]
    simp [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right (And.right functionality_typing))
    · apply hssS
    · apply hsS
    · apply hsS'
    · apply htT

-- theorem functionality_typing :
--     (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
--     (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {T : Tm (n + 1)} {s s' S : Tm l},
--       (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--       → (Γ ⬝ S ⊗ Δ ⊢ T type)
--       → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) ≡ (T⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) type
--     ) ∧
--     (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {t T : Tm (n + 1)} {s s' S : Tm l},
--       (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--       → (Γ ⬝ S ⊗ Δ ⊢ t ∶ T)
--       → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢
--         (t⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) ≡ (t⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) 
--         ∶ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉)
--     ) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A)) :=
--   by
--     suffices h :
--     (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
--         Γ ⊢ A type →
--           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
--             (eqM : n = m + 1),
--             (Γ_1 ⊢ s ≡ s' ∶ S) →
--               (Γ_1 ⊢ s ∶ S) →
--                 (Γ_1 ⊢ s' ∶ S) →
--                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
--       (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
--           (Γ ⊢ a ∶ A) →
--             ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--               (eqM : n = m + 1),
--               (Γ_1 ⊢ s ≡ s' ∶ S) →
--                 (Γ_1 ⊢ s ∶ S) →
--                   (Γ_1 ⊢ s' ∶ S) →
--                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                       eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) ∧
--         (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
--           ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A
--     by
--       any_goals repeat' (apply And.intro)
--       · intro n Γ hiC
--         apply hiC
--       · intro n l Γ Δ T s s' S hssS hsS hsS' hT
--         apply And.left (And.right h)
--         · apply hT
--         · apply hssS
--         · apply hsS
--         · apply hsS'
--         · rfl
--         · rfl
--         · rfl
--       · intro n l Γ Δ t T s s' S hssS hsS hsS' htT
--         apply And.left (And.right (And.right h))
--         · apply htT
--         · apply hssS
--         · apply hsS
--         · apply hsS'
--         · rfl
--         · rfl
--         · rfl
--         · rfl
--       · intro n Γ A A' hAA
--         apply hAA
--       · intro n Γ A a a' haaA
--         apply haaA
--     apply judgment_recursor
--       -- (motive_1 := fun {n} Γ' _hiC =>
--       --   (∀ (eqM : n = 0), eqM ▸ Γ' = ε → (ε ctx)) ∧
--       --   (∀m (Γ : Ctx m) (eqM : n = m + 1) B,
--       --     eqM ▸ Γ' = Γ ⬝ B →
--       --     (Γ ⊢ B ≡ B type)))
--       -- (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
--       -- (motive_3 := fun {n} Γ' a' A' _haA =>
--       --   (∀ (eqM : n = 0) A,
--       --     eqM ▸ Γ' = ε → eqM ▸ A' = A →
--       --     (ε ⊢ A ≡ A type)) ∧
--       --   (∀ (eqM : n = 0) a A,
--       --     eqM ▸ Γ' = ε → eqM ▸ a' = a → eqM ▸ A' = A →
--       --     (ε ⊢ a ≡ a ∶ A)) ∧
--       --   (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
--       --     eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
--       --     Γ ⊢ B ≡ B type) ∧
--       --   (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) A B,
--       --     eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ A' = A →
--       --     (Γ ⬝ B ⊗ Δ ⊢ A ≡ A type)) ∧
--       --   (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) a A B,
--       --     eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A' = A →
--       --     (Γ ⬝ B  ⊗ Δ ⊢ a ≡ a ∶ A))
--       -- )
--       (motive_1 := fun {n} Γ' _hiC => Γ' ctx)
--       (motive_2 := fun {n} Γ' A' _hA =>
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1)) (eqM : n = m + 1),
--         (Γ ⊢ s ≡ s' ∶ S)
--         → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--         → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = T
--         → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T⌈s'/ₙ (leq)⌉) type)
--       (motive_3 := fun {n} Γ' a' A' haA =>
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1)) (eqM : n = m + 1),
--         (Γ ⊢ s ≡ s' ∶ S)
--         → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--         → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = t → eqM ▸ A' = T
--         → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉))
--       (motive_4 := fun {n} Γ' C C' _hCC => Γ' ⊢ C ≡ C' type)
--       (motive_5 := fun {n} Γ' c c' C _haaA => Γ' ⊢ c ≡ c' ∶ C)
--     any_goals sorry

-- theorem functionality_typing_tt :
--   (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A type) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ a ∶ A) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
--             Γ ⊢ A ≡ A' type →
--               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
--                 (eqM : n = m + 1),
--                 (Γ_1 ⊢ s ≡ s' ∶ S) →
--                   (Γ_1 ⊢ s ∶ S) →
--                     (Γ_1 ⊢ s' ∶ S) →
--                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                         eqM ▸ A = T → eqM ▸ A' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
--   ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
--             (Γ ⊢ a ≡ a' ∶ A) →
--               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
--                 (eqM : n = m + 1),
--                 (Γ_1 ⊢ s ≡ s' ∶ S) →
--                   (Γ_1 ⊢ s ∶ S) →
--                     (Γ_1 ⊢ s' ∶ S) →
--                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
--                         eqM ▸ a = t →
--                           eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
--   by
--     apply judgment_recursor
--       (motive_1 := fun {n} Γ' _hiC => Γ' ctx)
--       (motive_2 := fun {n} Γ' A' _hA => Γ' ⊢ A' type)
--       (motive_3 := fun {n} Γ' a' A' haA => Γ' ⊢ a' ∶ A')
--       (motive_4 := fun {n} Γ' C C' _hCC =>
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1)) (eqM : n = m + 1),
--         (Γ ⊢ s ≡ s' ∶ S)
--         → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--         → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ C = T → eqM ▸ C' = T
--         → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T⌈s'/ₙ (leq)⌉) type)
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1)) (eqM : n = m + 1),
--         (Γ ⊢ s ≡ s' ∶ S)
--         → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--         → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ c = t → eqM ▸ c' = t → eqM ▸ C = T
--         → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉))
--     case IsEqualTermVarEq =>
--       apply functionality_typing_var_eq
--     any_goals sorry
--
--
--

