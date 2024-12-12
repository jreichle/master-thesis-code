import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.untyped.Weakening

import aesop

/- # Rules -/
-- 5 judgments:
-- - Γ ctx
-- - Γ ⊢ A type
-- - Γ ⊢ a : A
-- - Γ ⊢ A = A' type
-- - Γ ⊢ a = a' : A

mutual
  -- Γ ctx
  @[aesop unsafe [constructors]]
  inductive IsCtx : Ctx n → Prop where
    | empty : IsCtx .empty
    | extend : IsCtx Γ → IsType Γ A → IsCtx (Γ ⬝ A)

  -- Γ ⊢ A type
  @[aesop unsafe [constructors]]
  inductive IsType : Ctx n → Tm n → Prop where
    -- formation rules
    | unit_form : IsCtx Γ
                  → IsType Γ 𝟙
    | empty_form : IsCtx Γ
                   → IsType Γ 𝟘
    | pi_form : IsType Γ A → IsType (Γ ⬝ A) B
                → IsType Γ (.pi A B)
    | sigma_form : IsType Γ A → IsType (Γ ⬝ A) B
                   → IsType Γ (.sigma A B)
    | iden_form : HasType Γ a A → HasType Γ a' A
                  → IsType Γ (.iden A a a')
    | univ_form : IsCtx Γ
                  → IsType Γ 𝒰
    | univ_elim : HasType Γ A 𝒰
                  → IsType Γ A

  -- Γ ⊢ a : A
  @[aesop unsafe [constructors]]
  inductive HasType : Ctx n → Tm n → Tm n → Prop where
    -- structural rules
    -- make sure variables of A refer to to same variables of Γ as before with lifting
    | var : IsType Γ A
            → HasType (Γ ⬝ A) (.var 0) (weaken (.shift .id) A)
    -- | weak : HasType Γ (.var i) A → IsType Γ B
    --          → HasType (Γ ⬝ B) (.var (.succ i)) (weaken A (.shift .id))
    -- intro rules
    | unit_intro : IsCtx Γ
                   → HasType Γ .tt 𝟙
    | pi_intro : HasType (Γ ⬝ A) b B
                 → HasType Γ (.lam A b) (.pi A B)
    | sigma_intro : HasType Γ a A → HasType Γ b (substitute_zero B a)
                    → HasType Γ (.pairSigma a b) (.sigma A B)
    | iden_intro : HasType Γ a A
                   → HasType Γ (.refl A a) (.iden A a a)
    -- universe intro
    | univ_unit : IsCtx Γ
                  → HasType Γ 𝟙 𝒰
    | univ_empty : IsCtx Γ
                   → HasType Γ 𝟘 𝒰
    | univ_pi : HasType Γ A 𝒰 → HasType (Γ ⬝ A) B 𝒰
                → HasType Γ (.pi A B) 𝒰
    | univ_sigma : HasType Γ A 𝒰 → HasType (Γ ⬝ A) B 𝒰
                   → HasType Γ (.sigma A B) 𝒰
    | univ_iden : HasType Γ A 𝒰 → HasType Γ a A → HasType Γ a' A
                  → HasType Γ (.iden A a a') 𝒰
    -- elimination rules (except univ)
    | unit_elim : IsType (Γ ⬝ 𝟙) A → HasType Γ a (substitute_zero A .tt)
                  → HasType Γ b 𝟙
                  → HasType Γ (.indUnit A b a) (substitute_zero A b)
    | empty_elim : IsType (Γ ⬝ 𝟘) A → HasType Γ b 𝟘
                   → HasType Γ (.indEmpty A b) (substitute_zero A b)
    | pi_elim : HasType Γ f (.pi A B) → HasType Γ a A
                → HasType Γ (.app f a) (substitute_zero B a)
    | sigma_elim : HasType Γ p (.sigma A B) → IsType (Γ ⬝ (.sigma A B)) C
                   → HasType (Γ ⬝ A ⬝ B) c
                     (substitute ((.weak (.shift (.shift .id))), .pairSigma (.var 1) (.var 0)) C)
                   → HasType Γ (.indSigma A B C c p) (substitute_zero C p)
    | iden_elim : IsType (((Γ ⬝ A) ⬝ (weaken (.shift .id) A))
                    ⬝ (.iden (weaken (.shift (.shift .id)) A) (.var 1) (.var 0))) B
                  → HasType Γ b (substitute ( .weak .id, a, a, .refl A a) B)
                  → HasType Γ p (.iden A a a')
                  → HasType Γ (.j A B b a a' p) (substitute (.weak .id, a, a', p) B)
    -- conversion
    | ty_conv : HasType Γ a A → IsEqualType Γ A B
                → HasType Γ a B

  -- Γ ⊢ A ≡ B type
  @[aesop unsafe [constructors]]
  inductive IsEqualType : Ctx n → Tm n → Tm n → Prop where
    -- congruence rules (formation)
    | unit_form_eq : IsCtx Γ
                     → IsEqualType Γ 𝟙 𝟙
    | empty_form_eq : IsCtx Γ
                      → IsEqualType Γ 𝟘 𝟘
    | pi_form_eq : IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B'
                   → IsEqualType Γ (.pi A B) (.pi A' B')
    | sigma_form_eq : IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B'
                      → IsEqualType Γ (.sigma A B) (.sigma A' B')
    | iden_form_eq : IsEqualType Γ A A' → IsEqualTerm Γ a₁ a₂ A → IsEqualTerm Γ a₃ a₄ A'
                     → IsEqualType Γ (.iden A a₁ a₃) (.iden A' a₂ a₄)
    | univ_form_eq : IsCtx Γ
                     → IsEqualType Γ 𝒰 𝒰
    | univ_elim_eq : IsEqualTerm Γ A A' 𝒰 → IsEqualType Γ A A'

  -- Γ ⊢ a ≡ b : A
  @[aesop unsafe [constructors]]
  inductive IsEqualTerm : Ctx n → Tm n → Tm n → Tm n → Prop where
    | var_eq : IsType Γ A
                → IsEqualTerm (Γ ⬝ A) (.var 0) (.var 0) (weaken (.shift .id) A)
    -- computation rules
    | unit_comp : IsType (Γ ⬝ 𝟙) A → HasType Γ a (substitute_zero A .tt)
                  → IsEqualTerm Γ (.indUnit A .tt a) a (substitute_zero A .tt)
    | pi_comp : HasType (Γ ⬝ A) b B → HasType Γ a A
                → IsEqualTerm Γ (.app (.lam A b) a) (substitute_zero b a) (substitute_zero B a)
    | sigma_comp : HasType Γ a A → HasType Γ b (substitute_zero B a)
                   → IsType (Γ ⬝ (.sigma A B)) C
                   → HasType (Γ ⬝ A ⬝ B) c (
                       substitute ((.weak (.shift (.shift .id))), .pairSigma (.var 1) (.var 0)) C
                     )
                   → IsEqualTerm Γ (.indSigma A B C c (.pairSigma a b))
                     (substitute (.weak .id, a, b) c)
                     (substitute_zero C (.pairSigma a b))
    | iden_comp : IsType (((Γ ⬝ A) ⬝ (weaken (.shift .id) A))
                    ⬝ (.iden (weaken (.shift (.shift .id)) A) (.var 1) (.var 0))) B
                  → HasType Γ b
                    (substitute (.weak .id, a, a, (.refl A a)) B)
                  → HasType Γ a A
                  → IsEqualTerm Γ (.j A B b a a (.refl A a)) b
                    (substitute (.weak .id, a, a, (.refl A a)) B)
    -- congruence rules (introduction and elimination)
    | unit_intro_eq : IsCtx Γ
                      → IsEqualTerm Γ .tt .tt 𝟙
    | unit_elim_eq : IsEqualType (Γ ⬝ 𝟙) A A' → IsEqualTerm Γ a a' (substitute_zero A .tt)
                     → IsEqualTerm Γ b b' 𝟙
                     → IsEqualTerm Γ (.indUnit A b a) (.indUnit A' b' a') (substitute_zero A b)
    | empty_elim_eq : IsEqualType (Γ ⬝ 𝟘) A A' → IsEqualTerm Γ b b' 𝟘
                      → IsEqualTerm Γ (.indEmpty A b) (.indEmpty A' b') (substitute_zero A b)
    | pi_intro_eq : IsEqualTerm (Γ ⬝ A) b b' B
                    → IsEqualTerm Γ (.lam A b) (.lam A' b') (.pi A B)
    | pi_elim_eq : IsEqualTerm Γ f f' (.pi A B) → IsEqualTerm Γ a a' A
                   → IsEqualTerm Γ (.app f a) (.app f' a') (substitute_zero B a)
    | sigma_intro_eq : IsEqualTerm Γ a a' A → IsEqualTerm Γ b b' (substitute_zero B a)
                       → IsEqualTerm Γ (.pairSigma a b) (.pairSigma a' b') (.sigma A B)
    | sigma_elim_eq : IsEqualType Γ (.sigma A B) (.sigma A' B') 
                      → IsEqualTerm Γ p p' (.sigma A B)
                      → IsEqualType (Γ ⬝ (.sigma A B)) C C'
                      → IsEqualTerm (Γ ⬝ A ⬝ B) c c' (
                          substitute ((.weak (.shift (.shift .id))),
                                          .pairSigma (.var 1) (.var 0)) C
                        )
                      → IsEqualTerm Γ (.indSigma A B C c p) (.indSigma A' B' C' c' p')
                        (substitute_zero C p)
    | iden_intro_eq : IsEqualType Γ A A' → IsEqualTerm Γ a a' A
                      → IsEqualTerm Γ (.refl A a) (.refl A' a') (.iden A a a)
    | iden_elim_eq : IsEqualType (((Γ ⬝ A) ⬝ (weaken (.shift .id) A)) ⬝ (
                          .iden (weaken (.shift (.shift .id)) A) (.var 1) (.var 0)
                        )) B B'
                     → IsEqualTerm Γ b b' (substitute (.weak .id, a₁, a₁, .refl A a₁) B)
                     → IsEqualType Γ (.iden A a₁ a₃) (.iden A' a₂ a₄)
                     → IsEqualTerm Γ p p' (.iden A a₁ a₃)
                     → IsEqualTerm Γ (.j A B b a₁ a₃ p) (.j A' B' b' a₂ a₄ p')
                       (substitute (.weak .id, a₁, a₃, p) B)
    | univ_unit_eq : IsCtx Γ
                     → IsEqualTerm Γ 𝟙 𝟙 𝒰
    | univ_empty_eq : IsCtx Γ
                     → IsEqualTerm Γ 𝟘 𝟘 𝒰
    | univ_pi_eq : IsEqualTerm Γ A A' 𝒰 → IsEqualTerm (Γ ⬝ A) B B' 𝒰
                   → IsEqualTerm Γ (.pi A B) (.pi A' B') 𝒰
    | univ_sigma_eq : IsEqualTerm Γ A A' 𝒰 → IsEqualTerm (Γ ⬝ A) B B' 𝒰
                   → IsEqualTerm Γ (.sigma A B) (.sigma A' B') 𝒰
    | univ_iden_eq : IsEqualTerm Γ A A' 𝒰 → IsEqualTerm Γ a₁ a₂ A → IsEqualTerm Γ a₃ a₄ A 
                     → IsEqualTerm Γ (.iden A a₁ a₃) (.iden A' a₂ a₄) 𝒰
    -- conversion
    | ty_conv_eq : IsEqualTerm Γ a b A → IsEqualType Γ A B
                   → IsEqualTerm Γ a b B
end

postfix:90 " ctx" => IsCtx
notation:90 Γ " ⊢ " A  " type" => IsType Γ A
notation:90 Γ " ⊢ " s " ∶ " A => HasType Γ s A
notation:90 Γ " ⊢ " A " ≡ " B " type" => IsEqualType Γ A B
notation:90 Γ " ⊢ " s " ≡ " t " ∶ " A => IsEqualTerm Γ s t A
