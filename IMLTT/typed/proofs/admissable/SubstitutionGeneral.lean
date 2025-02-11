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

theorem lift_n_substitution {n : Nat} {leq : l ≤ n} {s : Tm l} :
    ⇑ₛn_substitution (leq := by omega) (n := n) s = n_substitution (leq := by omega) (n := n + 1) s :=
  by
    simp [n_substitution]
    split
    case isTrue h =>
      rfl
    case isFalse h =>
      apply False.elim
      omega

theorem tester : n ≤ m → n ≤ m + 1 := by omega

-- set_option pp.proofs true

theorem substitution_test :
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx (n + 2)} {s : Tm l},
    Γ ctx
    → ((get_sub_context (leq := by omega) Γ l) ⊢ s ∶ (get_from_context (leq := by omega) Γ l))
    → (remove_from_ctx (leq := by omega) Γ s) ctx) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx (n + 1)} {A : Tm (n + 1)} {s : Tm l},
    Γ ⊢ A type
    → ((get_sub_context (leq := by omega) Γ l) ⊢ s ∶ (get_from_context (leq := by omega) Γ l))
    → (remove_from_ctx (leq := by omega) Γ s) ⊢ A⌈n_substitution (leq := by omega) s⌉ type) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx (n + 1)} {A a : Tm (n + 1)} {s : Tm l},
    (Γ ⊢ a ∶ A)
    → ((get_sub_context (leq := by omega) Γ l) ⊢ s ∶ (get_from_context (leq := by omega) Γ l))
    → (remove_from_ctx (leq := by omega) Γ s) ⊢ a⌈n_substitution (leq := by omega) s⌉ ∶ A⌈n_substitution (leq := by omega) s⌉) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx (n + 1)} {A A' : Tm (n + 1)} {s : Tm l},
    (Γ ⊢ A ≡ A' type)
    → ((get_sub_context (leq := by omega) Γ l) ⊢ s ∶ (get_from_context (leq := by omega) Γ l))
    → (remove_from_ctx (leq := by omega) Γ s) ⊢ A⌈n_substitution (leq := by omega) s⌉ ≡ A'⌈n_substitution (leq := by omega) s⌉ type) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx (n + 1)} {A a a' : Tm (n + 1)} {s : Tm l},
    (Γ ⊢ a ≡ a' ∶ A)
    → ((get_sub_context (leq := by omega) Γ l) ⊢ s ∶ (get_from_context (leq := by omega) Γ l))
    → (remove_from_ctx (leq := by omega) Γ s) ⊢ a⌈n_substitution (leq := by omega) s⌉ ≡ a'⌈n_substitution (leq := by omega) s⌉  ∶ A⌈n_substitution (leq := by omega) s⌉) :=
  by
    suffices h :
      (∀ {n : Nat} {Γ : Ctx n} (isCtx : Γ ctx)
        (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx (m + 2)) (eqM : n = m + 2) (s : Tm l),
        eqM ▸ Γ = Γ_1 → (get_sub_context (leq := by omega) Γ_1 l ⊢ s ∶ get_from_context (leq := by omega) Γ_1 l) → remove_from_ctx (leq := by omega) Γ_1 s ctx) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A : Tm n} (isType : Γ ⊢ A type)
        (m l : Nat) (leq : l ≤ m) (Γ_1 : Ctx (m + 1)) (eqM : n = m + 1) {s : Tm l} (A_1 : Tm (m + 1)),
        eqM ▸ Γ = Γ_1 → eqM ▸ A = A_1
        → (get_sub_context (leq := by omega) Γ_1 l ⊢ s ∶ get_from_context (leq := by omega) Γ_1 l)
        → remove_from_ctx (leq := by omega) Γ_1 s ⊢ A_1⌈n_substitution (leq := by omega) s⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n} (hasType : Γ ⊢ a ∶ A)
        (m l : Nat) (leq : l ≤ m) (Γ_1 : Ctx (m + 1)) (eqM : n = m + 1) (s : Tm l) (a_1 A_1 : Tm (m + 1)),
        eqM ▸ Γ = Γ_1 → eqM ▸ a = a_1 → eqM ▸ A = A_1
        → (get_sub_context (leq := tester leq) Γ_1 l ⊢ s ∶ get_from_context (leq := leq) Γ_1 l)
        → remove_from_ctx (leq := leq) Γ_1 s ⊢ a_1⌈n_substitution (leq := leq) s⌉ ∶ A_1⌈n_substitution (leq := leq) s⌉) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} (isEqualType : Γ ⊢ A ≡ A' type)
        (m l : Nat) (leq : l ≤ m) (Γ_1 : Ctx (m + 1)) (eqM : n = m + 1) (s : Tm l) (A_1 A'_1 : Tm (m + 1)),
        eqM ▸ Γ = Γ_1 → eqM ▸ A = A_1 → eqM ▸ A' = A'_1
        → (get_sub_context (leq := by omega) Γ_1 l ⊢ s ∶ get_from_context (leq := by omega) Γ_1 l)
        → remove_from_ctx (leq := by omega) Γ_1 s ⊢ A_1⌈n_substitution (leq := by omega) s⌉ ≡ A'_1⌈n_substitution (leq := by omega) s⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n} (isEqualTerm : Γ ⊢ a ≡ a' ∶ A)
        (m l : Nat) (leq : l ≤ m) (Γ_1 : Ctx (m + 1)) (eqM : n = m + 1) (s : Tm l) (a_1 a'_1 A_1 : Tm (m + 1)),
        eqM ▸ Γ = Γ_1 → eqM ▸ a = a_1 → eqM ▸ a' = a'_1 → eqM ▸ A = A_1
        → (get_sub_context (leq := by omega) Γ_1 l ⊢ s ∶ get_from_context (leq := by omega) Γ_1 l)
        → remove_from_ctx (leq := by omega) Γ_1 s ⊢ a_1⌈n_substitution (leq := by omega) s⌉ ≡ a'_1⌈n_substitution (leq := by omega) s⌉ ∶ A_1⌈n_substitution (leq := by omega) s⌉)
      by
        any_goals repeat' (apply And.intro)
        · intro n l hleq Γ s hiCA hsS
          apply (And.left h)
          · apply hiCA
          · rfl
          · apply hsS
          · apply hleq
          · rfl
        · intro n l hleq Γ A s hA hsS
          apply And.left (And.right h)
          · apply hA
          · rfl
          · rfl
          · apply hsS
          · apply hleq
          · rfl
        · intro n l hleq Γ A a s haA hsS
          apply And.left (And.right (And.right h))
          · apply haA
          · rfl
          · rfl
          · rfl
          · apply hsS
          · rfl
        · intro n l hleq Γ A A' s hAA hsS
          apply And.left (And.right (And.right (And.right h)))
          · apply hAA
          · rfl
          · rfl
          · rfl
          · apply hsS
          · apply hleq
          · rfl
        · intro n l hleq Γ A a a' s haaA hsS
          apply And.right (And.right (And.right (And.right h)))
          · apply haaA
          · rfl
          · rfl
          · rfl
          · rfl
          · apply hsS
          · apply hleq
          · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx (m + 2)) (eqM : n = m + 2) s,
        eqM ▸ Γ' = Γ
        → ((get_sub_context Γ l (tester (tester leq))) ⊢ s ∶ (get_from_context Γ l (tester leq)))
        → ((remove_from_ctx (tester leq) Γ s) ctx))
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx (m + 1)) (eqM : n = m + 1) {s : Tm l} A,
        eqM ▸ Γ' = Γ → eqM ▸ A' = A
        → ((get_sub_context Γ l (tester leq)) ⊢ s ∶ (get_from_context Γ l leq))
        → (remove_from_ctx leq Γ s) ⊢ A⌈s/ₙ leq⌉ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx (m + 1)) (eqM : n = m + 1) s a A,
        eqM ▸ Γ' = Γ → eqM ▸ a' = a → eqM ▸ A' = A 
        → ((get_sub_context (leq := tester leq) Γ l) ⊢ s ∶ (get_from_context (leq := leq) Γ l))
        → (remove_from_ctx (leq := leq) Γ s) ⊢ (a⌈s/ₙ leq⌉) ∶ (A⌈s/ₙ leq⌉))
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx (m + 1)) (eqM : n = m + 1) s A A',
        eqM ▸ Γ' = Γ → eqM ▸ C = A → eqM ▸ C' = A'
        → ((get_sub_context Γ l (by omega)) ⊢ s ∶ (get_from_context Γ l (by omega)))
        → (remove_from_ctx (leq) Γ s) ⊢ (A⌈s/ₙ leq⌉) ≡ (A'⌈s/ₙ leq⌉) type)
      (motive_5 := fun {n} Γ' c c' C _haaA => 
        ∀ m l {leq : l ≤ m} (Γ : Ctx (m + 1)) (eqM : n = m + 1) s a a' A,
        eqM ▸ Γ' = Γ → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → ((get_sub_context Γ l (by omega)) ⊢ s ∶ (get_from_context Γ l leq))
        → (remove_from_ctx leq Γ s) ⊢ (a⌈s/ₙ leq⌉) ≡ (a'⌈s/ₙ leq⌉) ∶ (A⌈s/ₙ leq⌉))
    case IsCtxEmpty =>
      intro m l hleq Γ heqM s heqΓ hsS
      cases heqM
    case IsCtxExtend =>
      intro n Γ' A' hiC hA ihiC ihA m l hleq Γ heqM s heqΓ hsS
      cases heqM
      cases heqΓ
      simp_all
      rw [←extend_remove_from_context]
      apply IsCtx.extend
      · apply boundary_ctx_type 
        apply ihA m l  (leq := hleq)
        · rfl
        · rw [extend_get_sub_context] at hsS
          rw [extend_get_from_context leq] at hsS
          apply hsS
          any_goals omega
        · rfl
      · apply ihA m l (leq := hleq)
        · rfl
        · rw [extend_get_sub_context] at hsS
          rw [extend_get_from_context leq] at hsS
          apply hsS
          any_goals omega
        · rfl
    case IsTypeUnitForm =>
      intro n Γ' hiC ihiC m l hleq Γ heqM s A heqΓ heqA hsS
      cases heqM
      cases heqΓ
      cases heqA
      apply IsType.unit_form
      simp_all
      cases Γ' with
      | extend Δ' T =>
        rw [remove_from_ctx]
        split
        case isTrue h =>
          apply ctx_decr hiC
        case isFalse h =>
          cases m with
          | zero =>
            omega
          | succ m' =>
            simp_all
            rw [extend_remove_from_context]
            apply ihiC
            · rfl
            · apply hsS
            · omega
            · rfl
    case IsTypeEmptyForm =>
      intro n Γ' hiC ihiC m l hleq Γ heqM s A heqΓ heqA hsS
      cases heqM
      cases heqΓ
      cases heqA
      apply IsType.empty_form
      simp_all
      cases Γ' with
      | extend Δ' T =>
        rw [remove_from_ctx]
        split
        case isTrue h =>
          apply ctx_decr hiC
        case isFalse h =>
          cases m with
          | zero =>
            omega
          | succ m' =>
            simp_all
            rw [extend_remove_from_context]
            apply ihiC
            · rfl
            · apply hsS
            · omega
            · rfl
    case IsTypePiForm =>
      intro n Γ' A B hA hB ihA ihB m l hleq Γ heqM s Pi heqΓ heqPi hsS
      cases heqM
      rw [←heqΓ]
      rw [←heqPi]
      rw [substitute]
      apply IsType.pi_form
      · apply ihA
        · rfl
        · rfl
        · rw [heqΓ]
          apply hsS
        · exact hleq
        · rfl
      · simp [lift_subst_n]
        rw [lift_n_substitution]
        rw [extend_remove_from_context]
        apply ihB
        · rfl
        · rfl
        · rw [extend_get_sub_context]
          rw [extend_get_from_context]
          simp [heqΓ]
          apply hsS
          any_goals omega
        any_goals omega
    case IsTypeSigmaForm =>
      intro n Γ' A B hA hB ihA ihB m l hleq Γ heqM s Pi heqΓ heqPi hsS
      cases heqM
      rw [←heqΓ]
      rw [←heqPi]
      rw [substitute]
      apply IsType.sigma_form
      · apply ihA
        · rfl
        · rfl
        · rw [heqΓ]
          apply hsS
        · exact hleq
        · rfl
      · simp [lift_subst_n]
        rw [lift_n_substitution]
        rw [extend_remove_from_context]
        apply ihB
        · rfl
        · rfl
        · rw [extend_get_sub_context]
          rw [extend_get_from_context]
          simp [heqΓ]
          apply hsS
          any_goals omega
        any_goals omega
    case IsTypeIdenForm =>
      intro n Γ' a A a' haA haA' ihaA ihaA' m l hleq Γ heqM s Iden heqΓ heqIden hsS
      cases heqM
      rw [←heqΓ]
      rw [←heqIden]
      rw [substitute]
      apply IsType.iden_form
      · apply ihaA
        · rfl
        · rfl
        · rfl
        · rw [heqΓ]
          apply hsS
        · exact hleq
        · rfl
      · apply ihaA'
        · rfl
        · rfl
        · rfl
        · rw [heqΓ]
          apply hsS
        · exact hleq
        · rfl
    case IsTypeUnivForm =>
      intro n Γ' hiC ihiC m l hleq Γ heqM s U heqΓ heqU hsS
      cases heqM
      cases heqΓ
      cases heqU
      apply IsType.univ_form
      simp_all
      cases Γ' with
      | extend Δ' T =>
        rw [remove_from_ctx]
        split
        case isTrue h =>
          apply ctx_decr hiC
        case isFalse h =>
          cases m with
          | zero =>
            omega
          | succ m' =>
            simp_all
            rw [extend_remove_from_context]
            apply ihiC
            · rfl
            · apply hsS
            · omega
            · rfl
    case IsTypeUnivElim =>
      intro n Γ' A' hAU ihAU m l hleq Γ heqM s A heqΓ heqA hsS
      cases heqM
      cases heqΓ
      cases heqA
      apply IsType.univ_elim
      rw [←substitution_univ]
      apply ihAU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · exact hleq
      · rfl
    case HasTypeVar =>
      intro n Γ' A' hA ihA m l hleq Γ heqM s a A heqΓ heqa heqA hsS
      cases heqM
      cases heqΓ
      cases heqa
      cases heqA
      cases n with
      | zero =>
        rw [substitute]
        rw [n_substitution]
        simp_all
        simp [substitute_var]
        rw [head_remove_from_context]
        rw [extend_get_sub_context] at hsS
        have h : l = 0 := by omega
        rw [head_get_sub_context (eq := h)] at hsS -- explicitly give eq/leq proofs
        rw [head_get_from_context (eq := h)] at hsS
        rw [substitution_conv_zero]
        rw [substitution_shift_substitute_zero] -- get ... ▸ to rfl
        apply hsS
        any_goals omega
      | succ n' =>
        rw [substitute]
        rw [n_substitution]
        split
        case isTrue h =>
          rw [←extend_remove_from_context]
          simp [substitute_var]
          rw [substitution_shift_id_lift]
          apply HasType.var
          apply ihA
          · rfl
          · rfl
          · rw [extend_get_sub_context] at hsS
            simp [extend_get_from_context] at hsS
            rw [←extend_get_from_context]
            apply hsS
            any_goals omega
        case isFalse h =>
          simp_all
          simp [substitute_var]
          rw [head_remove_from_context]
          rw [extend_get_sub_context] at hsS
          rw [head_get_sub_context] at hsS
          rw [head_get_from_context] at hsS
          rw [substitution_conv_zero]
          rw [substitution_shift_substitute_zero]
          split
          case h_1 =>
            apply hsS
          case h_2 h =>
            -- aesop
            omega
          any_goals omega
    -- case HasTypeWeak =>
    --   intro n Γ' 
    --   sorry
    any_goals sorry
