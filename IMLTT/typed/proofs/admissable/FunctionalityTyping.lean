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

import IMLTT.typed.proofs.admissable.FunctionalityTyping.IsEqualType
import IMLTT.typed.proofs.admissable.FunctionalityTyping.IsEqualTerm
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
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
            (eqM : n = m + 1),
            (Γ_1 ⊢ s ≡ s' ∶ S) →
              (Γ_1 ⊢ s ∶ S) →
                (Γ_1 ⊢ s' ∶ S) →
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A
    by
      any_goals repeat' (apply And.intro)
      · intro n Γ hiC
        apply hiC
      · intro n l Γ Δ T s s' S hssS hsS hsS' hT
        apply And.left (And.right h)
        · apply hT
        · apply hssS
        · apply hsS
        · apply hsS'
        · rfl
        · rfl
        · rfl
      · intro n l Γ Δ t T s s' S hssS hsS hsS' htT
        apply And.left (And.right (And.right h))
        · apply htT
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
      (motive_1 := fun {n} Γ' _hiC => Γ' ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T⌈s'/ₙ (leq)⌉) type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = t → eqM ▸ A' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉))
      (motive_4 := fun {n} Γ' C C' _hCC => Γ' ⊢ C ≡ C' type)
      (motive_5 := fun {n} Γ' c c' C _haaA => Γ' ⊢ c ≡ c' ∶ C)
    any_goals sorry

-- theorem functionality_typing :
--   (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A type) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ a ∶ A) ∧
--   (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type →
--     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T T' : Tm (m + 1))
--       (eqM : n = m + 1),
--       (Γ_1 ⊢ s ≡ s' ∶ S) → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊢ s' ∶ S) → Γ_1 ⬝ S ⊗ Δ ⊢ T ≡ T' type →
--       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → eqM ▸ A' = T'
--       → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T'⌈s'/ₙleq⌉ type) ∧ -- XXX: T ≡ T
--   (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) →
--     ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t t' T : Tm (m + 1))
--     (eqM : n = m + 1),
--     (Γ_1 ⊢ s ≡ s' ∶ S) → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊢ s' ∶ S) → (Γ_1 ⬝ S ⊗ Δ ⊢ t ≡ t' ∶ T) →
--     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = t → eqM ▸ a' = t' → eqM ▸ A = T
--     → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t'⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) :=
--   by
--     apply judgment_recursor
--       (motive_1 := fun {n} Γ' _hiC => Γ' ctx)
--       (motive_2 := fun {n} Γ' A' _hA => Γ' ⊢ A' type)
--       (motive_3 := fun {n} Γ' a' A' haA => Γ' ⊢ a' ∶ A')
--       (motive_4 := fun {n} Γ' C C' _hCC =>
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T T' : Tm (m + 1)) (eqM : n = m + 1),
--         (Γ ⊢ s ≡ s' ∶ S)
--         → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--         → ((Γ ⬝ S ⊗ Δ) ⊢ T ≡ T' type)
--         → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ C = T → eqM ▸ C' = T'
--         → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T'⌈s'/ₙ (leq)⌉) type)
--       (motive_5 := fun {n} Γ' c c' C _haaA =>
--         ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t t' T : Tm (m + 1)) (eqM : n = m + 1),
--         (Γ ⊢ s ≡ s' ∶ S)
--         → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
--         → ((Γ ⬝ S ⊗ Δ) ⊢ t ≡ t' ∶ T)
--         → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ c = t → eqM ▸ c' = t' → eqM ▸ C = T
--         → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t'⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉))
--     case IsEqualTermVarEq =>
--       apply functionality_typing_var_eq
--     any_goals sorry
--
theorem functionality_typing_tt :
  (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A type) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ a ∶ A) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
            Γ ⊢ A ≡ A' type →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
                (eqM : n = m + 1),
                (Γ_1 ⊢ s ≡ s' ∶ S) →
                  (Γ_1 ⊢ s ∶ S) →
                    (Γ_1 ⊢ s' ∶ S) →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ A = T → eqM ▸ A' = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
  ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
            (Γ ⊢ a ≡ a' ∶ A) →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                (eqM : n = m + 1),
                (Γ_1 ⊢ s ≡ s' ∶ S) →
                  (Γ_1 ⊢ s ∶ S) →
                    (Γ_1 ⊢ s' ∶ S) →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ a = t →
                          eqM ▸ a' = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC => Γ' ctx)
      (motive_2 := fun {n} Γ' A' _hA => Γ' ⊢ A' type)
      (motive_3 := fun {n} Γ' a' A' haA => Γ' ⊢ a' ∶ A')
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ C = T → eqM ▸ C' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T⌈s'/ₙ (leq)⌉) type)
      (motive_5 := fun {n} Γ' c c' C _haaA =>
        ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ c = t → eqM ▸ c' = t → eqM ▸ C = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉))
    case IsEqualTermVarEq =>
      apply functionality_typing_var_eq
    any_goals sorry
