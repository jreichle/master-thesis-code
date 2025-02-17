import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening

import aesop

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A))
  :=
  by
    suffices h :
    (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
          ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (B : Tm m), eqM ▸ Γ = Γ_1 ⬝ B → Γ_1 ⊢ B ≡ B type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type) ∧
              (∀ (eqM : n = 0) (a_1 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_1 → eqM ▸ A = A_1 → ε ⊢ a_1 ≡ a_1 ∶ A_1) ∧
                (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
                    eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type) ∧
                  (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type) ∧
                    ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_1 A_1 : Tm z) (B : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_1 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_1 ≡ a_1 ∶ A_1) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A
    by
      any_goals repeat' apply And.intro
      · intro n Γ hiC
        apply hiC
      · intro n Γ A hA
        apply And.left (And.right h)
        apply hA
      · intro n Γ A a haA
        have ihbB := And.left (And.right (And.right h)) haA
        have ihεAA := And.left ihbB
        have ihεaaA := And.left (And.right ihbB)
        have ihΓBB := And.left (And.right (And.right ihbB))
        have ihΓAA := And.left (And.right (And.right (And.right ihbB)))
        have ihΓaaA := And.right (And.right (And.right (And.right ihbB)))
        cases Γ with
        | empty =>
          apply And.intro
          · apply ihεaaA
            any_goals rfl
          · apply ihεAA
            any_goals rfl
        | extend Γ S =>
          simp_all
          apply And.intro
          · rw [←empty_expand_context (Γ := Γ ⬝ S)]
            apply ihΓaaA
            any_goals rfl
          · rw [←empty_expand_context (Γ := Γ ⬝ S)]
            apply ihΓAA
            any_goals rfl
      · intro n Γ A A' hAA
        apply hAA
      · intro n Γ a a' A haaA
        apply haaA
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        (∀ (eqM : n = 0), eqM ▸ Γ' = ε → (ε ctx)) ∧
        (∀m (Γ : Ctx m) (eqM : n = m + 1) B,
          eqM ▸ Γ' = Γ ⬝ B →
          (Γ ⊢ B ≡ B type)))
      (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
      (motive_3 := fun {n} Γ' a' A' _haA =>
        (∀ (eqM : n = 0) A,
          eqM ▸ Γ' = ε → eqM ▸ A' = A →
          (ε ⊢ A ≡ A type)) ∧
        (∀ (eqM : n = 0) a A,
          eqM ▸ Γ' = ε → eqM ▸ a' = a → eqM ▸ A' = A →
          (ε ⊢ a ≡ a ∶ A)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          Γ ⊢ B ≡ B type) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ A' = A →
          (Γ ⬝ B ⊗ Δ ⊢ A ≡ A type)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) a A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A' = A →
          (Γ ⬝ B  ⊗ Δ ⊢ a ≡ a ∶ A))
      )
      (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
      (motive_5 := fun Γ a a' A _haaA => Γ ⊢ a ≡ a' ∶ A)
    case IsCtxEmpty =>
      apply And.intro
      · intro heqM heqΓ
        cases heqM
        cases heqΓ
        apply IsCtx.empty
      · intro n Γ heqM
        omega
    case IsCtxExtend =>
      intro n Γ' A hiC hA ihiC ihA
      apply And.intro
      · intro heqM
        omega
      · intro m Γ heqM B heqΓ
        cases heqM
        cases heqΓ
        apply ihA
    case IsTypeUnitForm =>
      intro n Γ hiC _ihiC
      apply IsEqualType.unit_form_eq hiC
    case IsTypeEmptyForm =>
      intro n Γ hiC _ihiC
      apply IsEqualType.empty_form_eq hiC
    case IsTypePiForm =>
      intro n Γ A B hA hB ihA ihB
      apply IsEqualType.pi_form_eq ihA ihB
    case IsTypeSigmaForm =>
      intro n Γ A B hA hB ihA ihB
      apply IsEqualType.sigma_form_eq ihA ihB
    case IsTypeIdenForm =>
      intro n Γ a A a' haA haA' ihaA ihaA'
      cases Γ with
      | empty =>
        aesop
      | extend Γ' B =>
        sorry
        -- aesop
    case IsTypeUnivForm =>
      intro n Γ hiC _ihiC
      apply IsEqualType.univ_form_eq hiC
    case IsTypeUnivElim =>
      intro n Γ A hAU ihAU
      cases Γ with
      | empty =>
        aesop
      | extend Γ' B =>
        sorry
    any_goals sorry

-- theorem defeq_refl :
--     (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ A ≡ A type))
--   :=
--   by
--     suffices h :
--     (∀ {n : Nat} {Γ : Ctx n},
--       Γ ctx →
--         (∀ (eqM : n = 0), eqM ▸ Γ = ε → ε ctx) ∧
--           ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (B : Tm m), eqM ▸ Γ = Γ_1 ⬝ B → Γ_1 ⊢ B ≡ B type) ∧
--     (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
--       (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
--           (Γ ⊢ a ∶ A) →
--             (∀ (eqM : n = 0) (a_1 A_1 : Tm 0),
--                 eqM ▸ Γ = ε → eqM ▸ a = a_1 → eqM ▸ A = A_1 → (ε ⊢ a_1 ≡ a_1 ∶ A_1) ∧ ε ⊢ A_1 ≡ A_1 type) ∧
--               ∀ (m : Nat) (Γ_1 : Ctx m) (eqM : n = m + 1) (a_1 A_1 : Tm (m + 1)) (B : Tm m),
--                 eqM ▸ Γ = Γ_1 ⬝ B →
--                   eqM ▸ a = a_1 →
--                     eqM ▸ A = A_1 → (Γ_1 ⬝ B ⊢ a_1 ≡ a_1 ∶ A_1) ∧ Γ_1 ⬝ B ⊢ A_1 ≡ A_1 type ∧ Γ_1 ⊢ B ≡ B type) ∧
--         (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
--           ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A
--       by
--         sorry
--     apply judgment_recursor
--       (motive_1 := fun {n} Γ' _hiC =>
--         (∀ (eqM : n = 0), eqM ▸ Γ' = ε → (ε ctx)) ∧
--         (∀m (Γ : Ctx m) (eqM : n = m + 1) B,
--           eqM ▸ Γ' = Γ ⬝ B →
--           (Γ ⊢ B ≡ B type)))
--       (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
--       (motive_3 := fun {n} Γ' a' A' _haA =>
--         (∀ (eqM : n = 0) a A,
--           eqM ▸ Γ' = ε → eqM ▸ a' = a → eqM ▸ A' = A →
--           (ε ⊢ a ≡ a ∶ A) ∧ (ε ⊢ A ≡ A type)) ∧
--         (∀ m (Γ : Ctx m) (eqM : n = m + 1) a A B,
--           eqM ▸ Γ' = Γ ⬝ B → eqM ▸ a' = a → eqM ▸ A' = A →
--           (Γ ⬝ B ⊢ a ≡ a ∶ A) ∧ (Γ ⬝ B ⊢ A ≡ A type) ∧ Γ ⊢ B ≡ B type))
--       (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
--       (motive_5 := fun Γ a a' A _haaA => Γ ⊢ a ≡ a' ∶ A)
--     case IsCtxEmpty =>
--       apply And.intro
--       · intro heqM heqΓ
--         cases heqM
--         cases heqΓ
--         apply IsCtx.empty
--       · intro n Γ heqM
--         omega
--     case IsCtxExtend =>
--       intro n Γ' A hiC hA ihiC ihA
--       apply And.intro
--       · intro heqM
--         omega
--       · intro m Γ heqM B heqΓ
--         cases heqM
--         cases heqΓ
--         apply ihA
--     case IsTypeUnitForm =>
--       intro n Γ hiC _ihiC
--       apply IsEqualType.unit_form_eq hiC
--     case IsTypeEmptyForm =>
--       intro n Γ hiC _ihiC
--       apply IsEqualType.empty_form_eq hiC
--     case IsTypePiForm =>
--       intro n Γ A B hA hB ihA ihB
--       apply IsEqualType.pi_form_eq ihA ihB
--     case IsTypeSigmaForm =>
--       intro n Γ A B hA hB ihA ihB
--       apply IsEqualType.sigma_form_eq ihA ihB
--     case IsTypeIdenForm =>
--       intro n Γ a A a' haA haA' ihaA ihaA'
--       cases Γ with
--       | empty =>
--         aesop
--       | extend Γ' B =>
--         aesop
--     case IsTypeUnivForm =>
--       intro n Γ hiC _ihiC
--       apply IsEqualType.univ_form_eq hiC
--     case IsTypeUnivElim =>
--       intro n Γ A hAU ihAU
--       cases Γ with
--       | empty =>
--         aesop
--       | extend Γ' B =>
--         aesop
--     case HasTypeVar =>
--       intro n Γ A hA ihA
--       apply And.intro
--       · intro eqM a' A' hEqΓ hEqa hEqA
--         simp [] at eqM
--       · intro n Γ' eqM a' A' B' hEqΓ hEqa hEqA
--         cases eqM
--         apply And.intro
--         · rw [←hEqΓ]
--           rw [←hEqa]
--           rw [←hEqA]
--           constructor
--           apply hA
--         · apply And.intro
--           · rw [←hEqΓ]
--             rw [←hEqA]
--             apply weakening_type_eq
--             · apply ihA
--             · apply hA
--           · have hiCA := IsCtx.extend (boundary_ctx_type hA) (hA)
--             aesop
--     case HasTypeWeak =>
--       sorry
--     case HasTypeUnitIntro =>
--       intro n Γ hiC ihiC
--       apply And.intro
--       · intro eqM a A hEqΓ hEqa hEqA
--         cases eqM
--         rw [←hEqa]
--         rw [←hEqA]
--         apply And.intro
--         · constructor
--           apply IsCtx.empty
--         · constructor
--           apply IsCtx.empty
--       · intro m Γ' eqM a' A' B' hEqΓ hEqa hEqA
--         cases eqM
--         cases hEqΓ
--         cases hEqa
--         cases hEqA
--         apply And.intro
--         · apply IsEqualTerm.unit_intro_eq
--           apply hiC
--         · apply And.intro
--           · constructor
--             apply hiC
--           · apply And.right ihiC
--             · rfl
--             · rfl
--     case HasTypePiIntro =>
--       intro n Γ A b B hbB ihbB
--       apply And.intro
--       · intro eqM a' A' hEqΓ hEqa hEqA 
--         cases eqM
--         cases hEqΓ
--         cases hEqa
--         cases hEqA
--         apply And.intro
--         · constructor
--           · aesop
--           · apply IsEqualType.pi_form_eq
--             · aesop
--             · have hr := And.right ihbB
--               have hEqM : 0 + 1 = 0 + 1 := by omega
--               have hEqΓ : ε ⬝ A = ε ⬝ A := by rfl
--               have hEqb : b = b := by rfl
--               have hEqB : B = B := by rfl
--               have h := hr 0 ε hEqM b B A hEqΓ hEqb hEqB
--               apply And.left (And.right h)
--         · apply IsEqualType.pi_form_eq
--           · aesop
--           · have hr := And.right ihbB
--             have hEqM : 0 + 1 = 0 + 1 := by omega
--             have hEqΓ : ε ⬝ A = ε ⬝ A := by rfl
--             have hEqb : b = b := by rfl
--             have hEqB : B = B := by rfl
--             have h := hr 0 ε hEqM b B A hEqΓ hEqb hEqB
--             apply And.left (And.right h)
--       · intro n Γ eqM a' A' B' hEqΓ hEqa hEqA
--         cases eqM
--         cases hEqΓ
--         cases hEqa
--         cases hEqA
--         apply And.intro
--         · apply IsEqualTerm.pi_intro_eq
--           · aesop
--           · apply IsEqualType.pi_form_eq
--             · aesop
--             · have hr := And.right ihbB
--               have hEqM : n + 1 + 1 = n + 1 + 1 := by omega
--               have hEqΓ : Γ ⬝ B' ⬝ A = Γ ⬝ B' ⬝ A := by rfl
--               have hEqb : b = b := by rfl
--               have hEqB : B = B := by rfl
--               have h := hr (n + 1) (Γ ⬝ B') hEqM b B A hEqΓ hEqb hEqB
--               apply And.left (And.right h)
--         · apply And.intro
--           · apply IsEqualType.pi_form_eq
--             · aesop
--             · have hr := And.right ihbB
--               have hEqM : n + 1 + 1 = n + 1 + 1 := by omega
--               have hEqΓ : Γ ⬝ B' ⬝ A = Γ ⬝ B' ⬝ A := by rfl
--               have hEqb : b = b := by rfl
--               have hEqB : B = B := by rfl
--               have h := hr (n + 1) (Γ ⬝ B') hEqM b B A hEqΓ hEqb hEqB
--               apply And.left (And.right h)
--           · have hr := And.right ihbB
--             have hEqM : n + 1 = n + 1 := by omega
--             have hEqΓ : Γ ⬝ B' ⬝ A = Γ ⬝ B' ⬝ A := by rfl
--             have hEqb : b = b := by rfl
--             have hEqB : B = B := by rfl
-- 
--             -- have h := hr (n) Γ hEqM b B A hEqΓ hEqb hEqB
--             -- have hB := ctx_extr (ctx_decr (boundary_ctx_term hbB))
--             -- have hB' := weakening_type hB hB
--             -- have hEqM : n + 1 + 1 = n + 1 + 1 := by omega
--             -- have hEqΓ : Γ ⬝ B' ⬝ A = Γ ⬝ B' ⬝ A := by rfl
--             -- have hEqb : b = b := by rfl
--             -- have hEqB : B = B := by rfl
--             -- have h := hr (n + 1) (Γ ⬝ B') hEqM b B (B'⌊↑ₚidₚ⌋)
--             sorry -- XXX: any idea?
--     case HasTypeSigmaIntro =>
--       sorry
--     case HasTypeUnitElim =>
--       sorry
--     case HasTypeEmptyElim =>
--       sorry
--     case HasTypePiElim =>
--       sorry
--     case HasTypeSigmaElim =>
--       sorry
--     case HasTypeIdenElim =>
--       sorry
--     case HasTypeUnivSigma =>
--       sorry
--     case HasTypeUnivIden =>
--       sorry
--     case HasTypeTyConv =>
--       sorry
--     any_goals sorry

theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
  by
    intro hA
    apply (And.left (And.right defeq_refl))
    apply hA

theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    have h := (And.left (And.right (And.right defeq_refl))) haA
    apply And.left h
