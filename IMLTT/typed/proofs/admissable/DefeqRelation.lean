import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.Contexts
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import aesop

/- # Definitional Equality is Equivalence Relation -/

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A) ∧ (Γ ⊢ A ≡ A type))
  :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => Γ ctx)
      (motive_2 := fun Γ A _hA => Γ ⊢ A ≡ A type)
      (motive_3 := fun Γ a A _haA => (Γ ⊢ a ≡ a ∶ A) ∧ (Γ ⊢ A ≡ A type))
      (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
      (motive_5 := fun Γ a a' A _haaA => (Γ ⊢ a ≡ a' ∶ A) ∧ (Γ ⊢ A ≡ A type))
    case IsCtxEmpty =>
      apply IsCtx.empty
    case IsCtxExtend =>
      intro n Γ A hiC hA _ihiC _ihA
      apply IsCtx.extend hiC hA
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
      apply IsEqualType.iden_form_eq
      · apply And.right ihaA
      · apply And.left ihaA
      · apply And.left ihaA'
    case IsTypeUnivForm =>
      intro n Γ hiC _ihiC
      apply IsEqualType.univ_form_eq hiC
    case IsTypeUnivElim =>
      intro n Γ A hAU ihAU
      apply IsEqualType.univ_elim_eq (And.left ihAU)
    case HasTypeVar =>
      intro n Γ A hA ihA
      apply And.intro
      · apply IsEqualTerm.var_eq hA
      · apply weakening_type_eq
        · apply ihA
        · apply hA
    case HasTypeUnitIntro =>
      intro n Γ hiC _ihiC
      apply And.intro
      · apply IsEqualTerm.unit_intro_eq hiC
      · apply IsEqualType.unit_form_eq hiC
    case HasTypePiIntro =>
      intro n Γ A b B hbB ihbB
      apply And.intro
      · apply IsEqualTerm.pi_intro_eq
        · apply And.left ihbB
      · apply IsEqualType.pi_form_eq
        · sorry -- FIXME: won't work
        · apply And.right ihbB
    case HasTypeSigmaIntro =>
      intro n Γ a A b B haA hbB ihaA ihbB
      apply And.intro
      · apply IsEqualTerm.sigma_intro_eq
        · apply And.left ihaA
        · apply And.left ihbB
      · apply IsEqualType.sigma_form_eq
        · apply And.right ihaA
        · apply substitution_inv_type_eq
          · rfl
          · rfl
          · apply And.right ihbB
          · apply haA
    case HasTypeIdenIntro =>
      intro n Γ A a haA ihaA
      apply And.intro
      · apply IsEqualTerm.iden_intro_eq
        · apply And.right ihaA
        · apply And.left ihaA
      · apply IsEqualType.iden_form_eq
        · apply And.right ihaA
        · apply And.left ihaA
        · apply And.left ihaA
    case HasTypeUnivUnit =>
      intro n Γ hiC _hiC
      apply And.intro
      · apply IsEqualTerm.univ_unit_eq hiC
      · apply IsEqualType.univ_form_eq hiC
    case HasTypeUnivEmpty =>
      intro n Γ hiC _hiC
      apply And.intro
      · apply IsEqualTerm.univ_empty_eq hiC
      · apply IsEqualType.univ_form_eq hiC
    case HasTypeUnivPi =>
      intro n Γ A B hAU hBU ihAU ihBU
      apply And.intro
      · apply IsEqualTerm.univ_pi_eq
        · apply And.left ihAU
        · apply And.left ihBU
      · apply And.right ihAU
    case HasTypeUnivSigma =>
      intro n Γ A B hAU hBU ihAU ihBU
      apply And.intro
      · apply IsEqualTerm.univ_sigma_eq
        · apply And.left ihAU
        · apply And.left ihBU
      · apply And.right ihAU
    case HasTypeUnivIden =>
      intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA'
      apply And.intro
      · apply IsEqualTerm.univ_iden_eq
        · apply And.left ihAU
        · apply And.left ihaA
        · apply And.left ihaA'
      · apply And.right ihAU
    case HasTypeUnitElim =>
      intro n Γ A a b hA haA hb1 ihA ihaA ihb1
      apply And.intro
      · apply IsEqualTerm.unit_elim_eq
        · apply ihA
        · apply And.left ihaA
        · apply And.left ihb1
      · sorry
    case HasTypeEmptyElim =>
      intro n Γ A b hA hb0 ihA ihb0
      apply And.intro
      · apply IsEqualTerm.empty_elim_eq
        · apply ihA
        · apply And.left ihb0
      · sorry
    case HasTypePiElim =>
      intro n Γ f A B a hfPi haA ihfPi ihaA
      apply And.intro
      · apply IsEqualTerm.pi_elim_eq
        · apply And.left ihfPi
        · apply And.left ihaA
      · sorry
    case HasTypeSigmaElim =>
      intro n Γ A B p C c hpSi hC hcC ihpSi ihC ihcC
      apply And.intro
      · apply IsEqualTerm.sigma_elim_eq
        · apply And.right ihpSi
        · apply And.left ihpSi
        · apply ihC
        · apply And.left ihcC
      · sorry
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p hB hbB hpId ihB ihbB ihpId
      apply And.intro
      · apply IsEqualTerm.iden_elim_eq
        · apply ihB
        · apply And.left ihbB
        · apply And.right ihpId
        · apply And.left ihpId
      · sorry
    case HasTypeTyConv =>
      intro n Γ a A B haA hAB ihaA ihAB
      apply And.intro
      · apply IsEqualTerm.ty_conv_eq
        · apply And.left ihaA
        · apply hAB
      · sorry -- FIXME: won't work


-- case IsEqualTypeUnitFormEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝟙 ≡ 𝟙 type
-- 
-- case IsEqualTypeEmptyFormEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝟘 ≡ 𝟘 type
-- 
-- case IsEqualTypePiFormEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
--   Γ ⊢ A ≡ A' type → Γ ⬝ A ⊢ B ≡ B' type → Γ ⊢ A ≡ A' type → Γ ⬝ A ⊢ B ≡ B' type → Γ ⊢ ΠA;B ≡ ΠA';B' type
-- 
-- case IsEqualTypeSigmaFormEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
--   Γ ⊢ A ≡ A' type → Γ ⬝ A ⊢ B ≡ B' type → Γ ⊢ A ≡ A' type → Γ ⬝ A ⊢ B ≡ B' type → Γ ⊢ ΣA;B ≡ ΣA';B' type
-- 
-- case IsEqualTypeIdenFormEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ A' : Tm n},
--   Γ ⊢ A ≡ A' type →
--     (Γ ⊢ a₁ ≡ a₂ ∶ A) →
--       (Γ ⊢ a₃ ≡ a₄ ∶ A') →
--         Γ ⊢ A ≡ A' type →
--           (Γ ⊢ a₁ ≡ a₂ ∶ A) ∧ Γ ⊢ A ≡ A type →
--             (Γ ⊢ a₃ ≡ a₄ ∶ A') ∧ Γ ⊢ A' ≡ A' type → Γ ⊢ A ℑ a₁ ≃ a₃ ≡ A' ℑ a₂ ≃ a₄ type
-- 
-- case IsEqualTypeUnivFormEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ U ≡ U type
-- 
-- case IsEqualTypeUnivElimEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, (Γ ⊢ A ≡ A' ∶ U) → (Γ ⊢ A ≡ A' ∶ U) ∧ Γ ⊢ U ≡ U type → Γ ⊢ A ≡ A' type
-- 
-- case IsEqualTermVarEq
-- ⊢ ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
--   Γ ⊢ A type → Γ ⊢ A ≡ A type → (Γ ⬝ A ⊢ v(0) ≡ v(0) ∶ A⌊↑id_⌋) ∧ Γ ⬝ A ⊢ A⌊↑id_⌋ ≡ A⌊↑id_⌋ type
-- 
-- case IsEqualTermUnitComp
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
--   Γ ⬝ 𝟙 ⊢ A type →
--     (Γ ⊢ a ∶ substitute_zero A ⋆) →
--       Γ ⬝ 𝟙 ⊢ A ≡ A type →
--         (Γ ⊢ a ≡ a ∶ substitute_zero A ⋆) ∧ Γ ⊢ substitute_zero A ⋆ ≡ substitute_zero A ⋆ type →
--           (Γ ⊢ A.indUnit ⋆ a ≡ a ∶ substitute_zero A ⋆) ∧ Γ ⊢ substitute_zero A ⋆ ≡ substitute_zero A ⋆ type
-- 
-- case IsEqualTermPiComp
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
--   (Γ ⬝ A ⊢ b ∶ B) →
--     (Γ ⊢ a ∶ A) →
--       (Γ ⬝ A ⊢ b ≡ b ∶ B) ∧ Γ ⬝ A ⊢ B ≡ B type →
--         (Γ ⊢ a ≡ a ∶ A) ∧ Γ ⊢ A ≡ A type →
--           (Γ ⊢ (λA; b)◃a ≡ substitute_zero b a ∶ substitute_zero B a) ∧
--             Γ ⊢ substitute_zero B a ≡ substitute_zero B a type
-- 
-- case IsEqualTermSigmaComp
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
--   (Γ ⊢ a ∶ A) →
--     (Γ ⊢ b ∶ substitute_zero B a) →
--       (Γ ⬝ ΣA;B) ⊢ C type →
--         (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈ₛ↑↑id_, (v(1)&v(0))⌉) →
--           (Γ ⊢ a ≡ a ∶ A) ∧ Γ ⊢ A ≡ A type →
--             (Γ ⊢ b ≡ b ∶ substitute_zero B a) ∧ Γ ⊢ substitute_zero B a ≡ substitute_zero B a type →
--               (Γ ⬝ ΣA;B) ⊢ C ≡ C type →
--                 (Γ ⬝ A ⬝ B ⊢ c ≡ c ∶ C⌈ₛ↑↑id_, (v(1)&v(0))⌉) ∧
--                     Γ ⬝ A ⬝ B ⊢ C⌈ₛ↑↑id_, (v(1)&v(0))⌉ ≡ C⌈ₛ↑↑id_, (v(1)&v(0))⌉ type →
--                   (Γ ⊢ A.indSigma B C c (a&b) ≡ c⌈ₛid_, a, b⌉ ∶ substitute_zero C (a&b)) ∧
--                     Γ ⊢ substitute_zero C (a&b) ≡ substitute_zero C (a&b) type
-- 
-- case IsEqualTermIdenComp
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a : Tm n},
--   (Γ ⬝ A ⬝ (A⌊↑id_⌋) ⬝ A⌊↑↑id_⌋ℑ v(1) ≃ v(0)) ⊢ B type →
--     (Γ ⊢ b ∶ B⌈ₛid_, a, a, A.refl a⌉) →
--       (Γ ⊢ a ∶ A) →
--         (Γ ⬝ A ⬝ (A⌊↑id_⌋) ⬝ A⌊↑↑id_⌋ℑ v(1) ≃ v(0)) ⊢ B ≡ B type →
--           (Γ ⊢ b ≡ b ∶ B⌈ₛid_, a, a, A.refl a⌉) ∧ Γ ⊢ B⌈ₛid_, a, a, A.refl a⌉ ≡ B⌈ₛid_, a, a, A.refl a⌉ type →
--             (Γ ⊢ a ≡ a ∶ A) ∧ Γ ⊢ A ≡ A type →
--               (Γ ⊢ A.j B b a a (A.refl a) ≡ b ∶ B⌈ₛid_, a, a, A.refl a⌉) ∧
--                 Γ ⊢ B⌈ₛid_, a, a, A.refl a⌉ ≡ B⌈ₛid_, a, a, A.refl a⌉ type
-- 
-- case IsEqualTermUnitIntroEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → (Γ ⊢ ⋆ ≡ ⋆ ∶ 𝟙) ∧ Γ ⊢ 𝟙 ≡ 𝟙 type
-- 
-- case IsEqualTermUnitElimEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
--   Γ ⬝ 𝟙 ⊢ A ≡ A' type →
--     (Γ ⊢ a ≡ a' ∶ substitute_zero A ⋆) →
--       (Γ ⊢ b ≡ b' ∶ 𝟙) →
--         Γ ⬝ 𝟙 ⊢ A ≡ A' type →
--           (Γ ⊢ a ≡ a' ∶ substitute_zero A ⋆) ∧ Γ ⊢ substitute_zero A ⋆ ≡ substitute_zero A ⋆ type →
--             (Γ ⊢ b ≡ b' ∶ 𝟙) ∧ Γ ⊢ 𝟙 ≡ 𝟙 type →
--               (Γ ⊢ A.indUnit b a ≡ A'.indUnit b' a' ∶ substitute_zero A b) ∧
--                 Γ ⊢ substitute_zero A b ≡ substitute_zero A b type
-- 
-- case IsEqualTermEmptyElimEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
--   Γ ⬝ 𝟘 ⊢ A ≡ A' type →
--     (Γ ⊢ b ≡ b' ∶ 𝟘) →
--       Γ ⬝ 𝟘 ⊢ A ≡ A' type →
--         (Γ ⊢ b ≡ b' ∶ 𝟘) ∧ Γ ⊢ 𝟘 ≡ 𝟘 type →
--           (Γ ⊢ A.indEmpty b ≡ A'.indEmpty b' ∶ substitute_zero A b) ∧ Γ ⊢ substitute_zero A b ≡ substitute_zero A b type
-- 
-- case IsEqualTermPiIntroEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b b' B : Tm (n + 1)} {A' : Tm n},
--   (Γ ⬝ A ⊢ b ≡ b' ∶ B) → (Γ ⬝ A ⊢ b ≡ b' ∶ B) ∧ Γ ⬝ A ⊢ B ≡ B type → (Γ ⊢ λA; b ≡ λA'; b' ∶ ΠA;B) ∧ Γ ⊢ ΠA;B ≡ ΠA;B type
-- 
-- case IsEqualTermPiElimEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
--   (Γ ⊢ f ≡ f' ∶ ΠA;B) →
--     (Γ ⊢ a ≡ a' ∶ A) →
--       (Γ ⊢ f ≡ f' ∶ ΠA;B) ∧ Γ ⊢ ΠA;B ≡ ΠA;B type →
--         (Γ ⊢ a ≡ a' ∶ A) ∧ Γ ⊢ A ≡ A type →
--           (Γ ⊢ f◃a ≡ f'◃a' ∶ substitute_zero B a) ∧ Γ ⊢ substitute_zero B a ≡ substitute_zero B a type
-- 
-- case IsEqualTermSigmaIntroEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
--   (Γ ⊢ a ≡ a' ∶ A) →
--     (Γ ⊢ b ≡ b' ∶ substitute_zero B a) →
--       (Γ ⊢ a ≡ a' ∶ A) ∧ Γ ⊢ A ≡ A type →
--         (Γ ⊢ b ≡ b' ∶ substitute_zero B a) ∧ Γ ⊢ substitute_zero B a ≡ substitute_zero B a type →
--           (Γ ⊢ a&b ≡ a'&b' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B ≡ ΣA;B type
-- 
-- case IsEqualTermSigmaElimEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
--   {c c' : Tm (n + 1 + 1)},
--   Γ ⊢ ΣA;B ≡ ΣA';B' type →
--     (Γ ⊢ p ≡ p' ∶ ΣA;B) →
--       (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
--         (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈ₛ↑↑id_, (v(1)&v(0))⌉) →
--           Γ ⊢ ΣA;B ≡ ΣA';B' type →
--             (Γ ⊢ p ≡ p' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B ≡ ΣA;B type →
--               (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
--                 (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈ₛ↑↑id_, (v(1)&v(0))⌉) ∧
--                     Γ ⬝ A ⬝ B ⊢ C⌈ₛ↑↑id_, (v(1)&v(0))⌉ ≡ C⌈ₛ↑↑id_, (v(1)&v(0))⌉ type →
--                   (Γ ⊢ A.indSigma B C c p ≡ A'.indSigma B' C' c' p' ∶ substitute_zero C p) ∧
--                     Γ ⊢ substitute_zero C p ≡ substitute_zero C p type
-- 
-- case IsEqualTermIdenIntroEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
--   Γ ⊢ A ≡ A' type →
--     (Γ ⊢ a ≡ a' ∶ A) →
--       Γ ⊢ A ≡ A' type →
--         (Γ ⊢ a ≡ a' ∶ A) ∧ Γ ⊢ A ≡ A type → (Γ ⊢ A.refl a ≡ A'.refl a' ∶ A ℑ a ≃ a) ∧ Γ ⊢ A ℑ a ≃ a ≡ A ℑ a ≃ a type
-- 
-- case IsEqualTermIdenElimEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' a₁ a₃ A' a₂ a₄ p p' : Tm n},
--   (Γ ⬝ A ⬝ (A⌊↑id_⌋) ⬝ A⌊↑↑id_⌋ℑ v(1) ≃ v(0)) ⊢ B ≡ B' type →
--     (Γ ⊢ b ≡ b' ∶ B⌈ₛid_, a₁, a₁, A.refl a₁⌉) →
--       Γ ⊢ A ℑ a₁ ≃ a₃ ≡ A' ℑ a₂ ≃ a₄ type →
--         (Γ ⊢ p ≡ p' ∶ A ℑ a₁ ≃ a₃) →
--           (Γ ⬝ A ⬝ (A⌊↑id_⌋) ⬝ A⌊↑↑id_⌋ℑ v(1) ≃ v(0)) ⊢ B ≡ B' type →
--             (Γ ⊢ b ≡ b' ∶ B⌈ₛid_, a₁, a₁, A.refl a₁⌉) ∧
--                 Γ ⊢ B⌈ₛid_, a₁, a₁, A.refl a₁⌉ ≡ B⌈ₛid_, a₁, a₁, A.refl a₁⌉ type →
--               Γ ⊢ A ℑ a₁ ≃ a₃ ≡ A' ℑ a₂ ≃ a₄ type →
--                 (Γ ⊢ p ≡ p' ∶ A ℑ a₁ ≃ a₃) ∧ Γ ⊢ A ℑ a₁ ≃ a₃ ≡ A ℑ a₁ ≃ a₃ type →
--                   (Γ ⊢ A.j B b a₁ a₃ p ≡ A'.j B' b' a₂ a₄ p' ∶ B⌈ₛid_, a₁, a₃, p⌉) ∧
--                     Γ ⊢ B⌈ₛid_, a₁, a₃, p⌉ ≡ B⌈ₛid_, a₁, a₃, p⌉ type
-- 
-- case IsEqualTermUnivUnitEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → (Γ ⊢ 𝟙 ≡ 𝟙 ∶ U) ∧ Γ ⊢ U ≡ U type
-- 
-- case IsEqualTermUnivEmptyEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → (Γ ⊢ 𝟘 ≡ 𝟘 ∶ U) ∧ Γ ⊢ U ≡ U type
-- 
-- case IsEqualTermUnivPiEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
--   (Γ ⊢ A ≡ A' ∶ U) →
--     (Γ ⬝ A ⊢ B ≡ B' ∶ U) →
--       (Γ ⊢ A ≡ A' ∶ U) ∧ Γ ⊢ U ≡ U type →
--         (Γ ⬝ A ⊢ B ≡ B' ∶ U) ∧ Γ ⬝ A ⊢ U ≡ U type → (Γ ⊢ ΠA;B ≡ ΠA';B' ∶ U) ∧ Γ ⊢ U ≡ U type
-- 
-- case IsEqualTermUnivSigmaEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
--   (Γ ⊢ A ≡ A' ∶ U) →
--     (Γ ⬝ A ⊢ B ≡ B' ∶ U) →
--       (Γ ⊢ A ≡ A' ∶ U) ∧ Γ ⊢ U ≡ U type →
--         (Γ ⬝ A ⊢ B ≡ B' ∶ U) ∧ Γ ⬝ A ⊢ U ≡ U type → (Γ ⊢ ΣA;B ≡ ΣA';B' ∶ U) ∧ Γ ⊢ U ≡ U type
-- 
-- case IsEqualTermUnivIdenEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
--   (Γ ⊢ A ≡ A' ∶ U) →
--     (Γ ⊢ a₁ ≡ a₂ ∶ A) →
--       (Γ ⊢ a₃ ≡ a₄ ∶ A) →
--         (Γ ⊢ A ≡ A' ∶ U) ∧ Γ ⊢ U ≡ U type →
--           (Γ ⊢ a₁ ≡ a₂ ∶ A) ∧ Γ ⊢ A ≡ A type →
--             (Γ ⊢ a₃ ≡ a₄ ∶ A) ∧ Γ ⊢ A ≡ A type → (Γ ⊢ A ℑ a₁ ≃ a₃ ≡ A' ℑ a₂ ≃ a₄ ∶ U) ∧ Γ ⊢ U ≡ U type
-- 
-- case IsEqualTermTyConvEq
-- ⊢ ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
--   (Γ ⊢ a ≡ b ∶ A) →
--     Γ ⊢ A ≡ B type → (Γ ⊢ a ≡ b ∶ A) ∧ Γ ⊢ A ≡ A type → Γ ⊢ A ≡ B type → (Γ ⊢ a ≡ b ∶ B) ∧ Γ ⊢ B ≡ B type
--
    any_goals sorry

theorem defeq_type_refl : IsType Γ A → IsEqualType Γ A A :=
  by
    intro hA
    apply (And.left (And.right defeq_refl))
    apply hA

theorem defeq_term_refl : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    -- apply And.left (And.left (And.right (And.right defeq_refl)))
    -- apply haA
    sorry

theorem defeq_term_symm : IsEqualTerm Γ a b A → IsEqualTerm Γ b a A :=
  by
    intro habA
    match habA with
    | .var_eq hA => sorry
    | .unit_comp hC hcC => sorry
    | .pi_comp hbB haA => sorry
    | .sigma_comp haA hbB hC hcC => sorry
    | .iden_comp hB hbB haA  => sorry
    | .unit_intro_eq hiC => sorry
    | .unit_elim_eq hAA haaA hbbUn => sorry
    | .empty_elim_eq hAA hbbEm => sorry
    | .pi_intro_eq hbbB => sorry
    | .pi_elim_eq haaA hffPi => sorry
    | .sigma_intro_eq haaA hbbB => sorry
    | .sigma_elim_eq hSiSi hppSi hCC hccC => sorry
    | .iden_intro_eq hAA haaA  => sorry
    | .iden_elim_eq hBB hbbB hIdId hppId => sorry
    | .univ_unit_eq hiC => sorry
    | .univ_empty_eq hiC => sorry
    | .univ_pi_eq hAAU hBBU => sorry
    | .univ_sigma_eq hAAU hBBU => sorry
    | .univ_iden_eq hAAU haaA haaA' => sorry
    | .ty_conv_eq habA hAB => sorry

theorem defeq_type_symm : IsEqualType Γ A B → IsEqualType Γ B A :=
  fun hABet : IsEqualType Γ A B ↦
    match hABet with
    | .unit_form_eq hic =>
      by
        apply IsEqualType.unit_form_eq hic
    | .empty_form_eq hic =>
      by
        apply IsEqualType.empty_form_eq hic
    | .pi_form_eq hAA hBB =>
      by
        apply IsEqualType.pi_form_eq
        · apply defeq_type_symm hAA
        · have hBB' := by apply context_conv_is_equal_type hBB hAA
          apply defeq_type_symm hBB'
    | .sigma_form_eq hAA hBB =>
      by
        apply IsEqualType.sigma_form_eq
        · apply defeq_type_symm hAA
        · have hBB' := by apply context_conv_is_equal_type hBB hAA
          apply defeq_type_symm hBB'
    | .iden_form_eq hAA haaA haaA' =>
      by
        apply IsEqualType.iden_form_eq
        · apply defeq_type_symm hAA
        · apply IsEqualTerm.ty_conv_eq (defeq_term_symm haaA) hAA
        · apply IsEqualTerm.ty_conv_eq (defeq_term_symm haaA') (defeq_type_symm hAA)
    | .univ_form_eq hic =>
      by
        apply IsEqualType.univ_form_eq hic
    | .univ_elim_eq hAAU =>
      by
        apply IsEqualType.univ_elim_eq
        apply defeq_term_symm
        apply hAAU


theorem defeq_term_trans : IsEqualTerm Γ a b A → IsEqualTerm Γ b c A → IsEqualTerm Γ a c A :=
  by
    intro habA hbcA
    sorry
    -- match habA with
    -- | .var_eq hA => sorry
    -- | .unit_comp hC hcC => sorry
    -- | .pi_comp hbB haA => sorry
    -- | .sigma_comp haA hbB hC hcC => sorry
    -- | .iden_comp hB hbB haA => sorry
    -- | .unit_intro_eq hiC => sorry
    -- | .unit_elim_eq hAA haaA hbbUn => sorry
    -- | .empty_elim_eq hAA hbbEm => sorry
    -- | .pi_intro_eq hAA hBB hbbB => sorry
    -- | .pi_elim_eq hPiPi haaA hffPi => sorry
    -- | .sigma_intro_eq hAA hBB haaA hbbB => sorry
    -- | .sigma_elim_eq hSiSi hppSi hCC hccC => sorry
    -- | .iden_intro_eq hAA  => sorry
    -- | .iden_elim_eq hAA hBB hbbB => sorry
    -- | .ty_conv_eq habA hAB => sorry


theorem defeq_type_trans : IsEqualType Γ A B → IsEqualType Γ B C → IsEqualType Γ A C :=
  fun hAB : IsEqualType Γ A B ↦
    fun hBC : IsEqualType Γ B C ↦
    match hAB with
    | .unit_form_eq hic =>
      by
        apply hBC
    | .empty_form_eq hic =>
      by
        apply hBC
    | .pi_form_eq hAA hBB =>
      by
        cases hBC with
        | pi_form_eq hAAc hBBc =>
          apply IsEqualType.pi_form_eq
          · apply defeq_type_trans hAA hAAc
          · have hBBs := context_conv_is_equal_type hBBc (defeq_type_symm hAA)
            apply defeq_type_trans hBB hBBs
        | univ_elim_eq hPiC =>
          apply IsEqualType.univ_elim_eq
          have hPiPi := (IsEqualType.pi_form_eq hAA hBB)
          sorry -- apply defeq_term_trans hPiPi hPiC
       --  sorry -- TODO: stuck? looping here -> use term transitivity
       --                                     -> inversions lemma (C gleich Pi), dann rausziehen
    | .sigma_form_eq hAA hBB =>
      by
        sorry
    | .iden_form_eq hAA haaA haaA' =>
      by
        sorry
    | .univ_form_eq hic =>
      by
        apply hBC
    | .univ_elim_eq hAAU =>
      by
        sorry
