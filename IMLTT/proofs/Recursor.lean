import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

set_option pp.proofs true

theorem judgment_recursor :
  ∀ {motive_1 : {n : Nat} → (Γ : Ctx n) → IsCtx Γ → Prop}
    {motive_2 : {n : Nat} → (Γ : Ctx n) → (A : Tm n) → IsType Γ A → Prop}
    {motive_3 : {n : Nat} → (Γ : Ctx n) → (a A : Tm n) → HasType Γ a A → Prop}
    {motive_4 : {n : Nat} → (Γ : Ctx n) → (A A' : Tm n) → IsEqualType Γ A A' → Prop}
    {motive_5 : {n : Nat} → (Γ : Ctx n) → (a a' A : Tm n) → IsEqualTerm Γ a a' A → Prop},
  (IsCtxEmpty : motive_1 ε IsCtx.empty)
  → (IsCtxExtend : ∀ {x : Nat} {Γ : Ctx x} {A : Tm x} (a : Γ ctx) (a_1 : Γ ⊢ A type),
    motive_1 Γ a → motive_2 Γ A a_1 → motive_1 (Γ ⬝ A) (IsCtx.extend a a_1))
  → (IsTypeUnitForm : ∀ {n : Nat} {Γ : Ctx n} (a : Γ ctx), 
    motive_1 Γ a → motive_2 Γ 𝟙 (IsType.unit_form a))
  → (IsTypeEmptyForm : ∀ {n : Nat} {Γ : Ctx n} (a : Γ ctx), 
    motive_1 Γ a → motive_2 Γ 𝟘 (IsType.empty_form a))
  → (IsTypePiForm : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)}
    (a : Γ ⊢ A type) (a_1 : (Γ ⬝ A) ⊢ B type), 
    motive_2 Γ A a → motive_2 (Γ ⬝ A) B a_1 → motive_2 Γ (.pi A B) (IsType.pi_form a a_1))
  → (IsTypeSigmaForm : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} 
    (a : Γ ⊢ A type) (a_1 : (Γ ⬝ A) ⊢ B type),
    motive_2 Γ A a → motive_2 (Γ ⬝ A) B a_1 → motive_2 Γ (.sigma A B) (IsType.sigma_form a a_1))
  → (IsTypeIdenForm : ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n}
    (a_1 : Γ ⊢ a ∶ A) (a_2 : Γ ⊢ a' ∶ A),
    motive_3 Γ a A a_1 → motive_3 Γ a' A a_2 → motive_2 Γ (.iden A a a') (IsType.iden_form a_1 a_2))
  → (IsTypeUnivForm : ∀ {n : Nat} {Γ : Ctx n}
    (a : Γ ctx), motive_1 Γ a → motive_2 Γ U (IsType.univ_form a))
  → (IsTypeUnivElim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} (a : Γ ⊢ A ∶ U),
    motive_3 Γ A U a → motive_2 Γ A (IsType.univ_elim a))
  → (HasTypeVar : ∀ {x : Nat} {Γ : Ctx x} {A : Tm x} 
    (a : Γ ⊢ A type), motive_2 Γ A a → motive_3 (Γ ⬝ A) v(0) (weaken A (.shift .id)) (HasType.var a))
  → (HasTypeUnitIntro : ∀ {n : Nat} {Γ : Ctx n}
    (a : Γ ctx), motive_1 Γ a → motive_3 Γ ⋆ 𝟙 (HasType.unit_intro a))
  → (HasTypePiIntro : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} 
    (a : (Γ ⬝ A) ⊢ b ∶ B), motive_3 (Γ ⬝ A) b B a → motive_3 Γ (.lam A b) (.pi A B) (HasType.pi_intro a))
  → (HasTypeSigmaIntro : ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)} 
    (a_1 : Γ ⊢ a ∶ A) (a_2 : Γ ⊢ b ∶ substitute_zero B a),
    motive_3 Γ a A a_1 → motive_3 Γ b (substitute_zero B a) a_2
    → motive_3 Γ (.pairSigma a b) (.sigma A B) (HasType.sigma_intro a_1 a_2))
  → (HasTypeIdenIntro : ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n} 
    (a_1 : Γ ⊢ A type) (a_2 : Γ ⊢ a ∶ A),
    motive_2 Γ A a_1 → motive_3 Γ a A a_2 
    → motive_3 Γ (.refl A a) (.iden A a a) (HasType.iden_intro a_1 a_2))
  → (HasTypeUnivUnit : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_3 Γ 𝟙 U (HasType.univ_unit a))
  → (HasTypeUnivEmpty : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_3 Γ 𝟘 U (HasType.univ_empty a))
  → (HasTypeUnivPi : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} 
    (a : Γ ⊢ A ∶ U) (a_1 : (Γ ⬝ A) ⊢ B ∶ U),
    motive_3 Γ A U a → motive_3 (Γ ⬝ A) B U a_1 → motive_3 Γ (.pi A B) U (HasType.univ_pi a a_1))
  → (HasTypeUnivSigma : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} 
    (a : Γ ⊢ A ∶ U) (a_1 : (Γ ⬝ A) ⊢ B ∶ U),
    motive_3 Γ A U a → motive_3 (Γ ⬝ A) B U a_1 → motive_3 Γ (.sigma A B) U (HasType.univ_sigma a a_1))
  → (HasTypeUnivIden : ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n} 
    (a_1 : Γ ⊢ A ∶ U) (a_2 : Γ ⊢ a ∶ A) (a_3 : Γ ⊢ a' ∶ A),
    motive_3 Γ A U a_1 → motive_3 Γ a A a_2 → motive_3 Γ a' A a_3 
    → motive_3 Γ (.iden A a a') U (HasType.univ_iden a_1 a_2 a_3))
  → (HasTypeUnitElim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n} 
    (a_1 : (Γ ⬝ 𝟙) ⊢ A type) (a_2 : Γ ⊢ a ∶ substitute_zero A ⋆) (a_3 : Γ ⊢ b ∶ 𝟙),
    motive_2 (Γ ⬝ 𝟙) A a_1 → motive_3 Γ a (substitute_zero A ⋆) a_2 → motive_3 Γ b 𝟙 a_3 
    → motive_3 Γ (.indUnit A b a) (substitute_zero A b) (HasType.unit_elim a_1 a_2 a_3))
  → (HasTypeEmptyElim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n} 
    (a : (Γ ⬝ 𝟘) ⊢ A type) (a_1 : Γ ⊢ b ∶ 𝟘), 
    motive_2 (Γ ⬝ 𝟘) A a → motive_3 Γ b 𝟘 a_1 
    → motive_3 Γ (.indEmpty A b) (substitute_zero A b) (HasType.empty_elim a a_1))
  → (HasTypePiElim : ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n} 
    (a_1 : Γ ⊢ f ∶ (.pi A B)) (a_2 : Γ ⊢ a ∶ A),
    motive_3 Γ f (.pi A B) a_1 → motive_3 Γ a A a_2 
    → motive_3 Γ (.app f a) (substitute_zero B a) (HasType.pi_elim a_1 a_2))
  → (HasTypeSigmaElim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} 
    {C : Tm (n + 1)} {c : Tm (n + 1 + 1)}
    (a : Γ ⊢ (.sigma A B) type) (a_1 : Γ ⊢ p ∶ (.sigma A B)) (a_2 : (Γ ⬝ (.sigma A B)) ⊢ C type)
    (a_3 : (Γ ⬝ A ⬝ B) ⊢ c ∶ (substitute C (Subst.weak (.shift (.shift .id)), (.pairSigma v(1) v(0))))),
    motive_2 Γ (.sigma A B) a → motive_3 Γ p (.sigma A B) a_1 → motive_2 (Γ ⬝ (.sigma A B)) C a_2
    → motive_3 (Γ ⬝ A ⬝ B) c
      (substitute C (Subst.weak (.shift (.shift .id)), (.pairSigma v(1) v(0)))) a_3
    → motive_3 Γ (.indSigma A B C c p) (substitute_zero C p) (HasType.sigma_elim a a_1 a_2 a_3) )
  → (HasTypeIdenElim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm n} 
    {a a' p : Tm n}
    (a_1 : (Γ ⬝ A ⬝ weaken A Weak.id.shift ⬝ (weaken A Weak.id.shift.shift).iden v(1) v(0)) ⊢ B type)
    (a_2 : Γ ⊢ b ∶ substitute B (Subst.weak .id, a, a', p))
    (a_3 : Γ ⊢ A.iden a a' type) (a_4 : Γ ⊢ p ∶ A.iden a a'),
    motive_2 (Γ ⬝ A ⬝ weaken A Weak.id.shift ⬝ (weaken A Weak.id.shift.shift).iden v(1) v(0)) B a_1 
    → motive_3 Γ b (substitute B (Subst.weak .id, a, a', p)) a_2
    → motive_2 Γ (A.iden a a') a_3 → motive_3 Γ p (A.iden a a') a_4 
    → motive_3 Γ (A.j B b a a' p) (substitute B (Subst.weak Weak.id, a, a', p)) 
      (HasType.iden_elim a_1 a_2 a_3 a_4))
  → (HasTypeTyConv : ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n}
    (a_1 : Γ ⊢ a ∶ A) (a_2 : Γ ⊢ A ≡ B type), 
    motive_3 Γ a A a_1 → motive_4 Γ A B a_2 
    → motive_3 Γ a B (HasType.ty_conv a_1 a_2))
  → (IsEqualTypeUnitFormEq : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_4 Γ 𝟙 𝟙 (IsEqualType.unit_form_eq a))
  → (IsEqualTypeEmptyFormEq: ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_4 Γ 𝟘 𝟘 (IsEqualType.empty_form_eq a))
  → (IsEqualTypePiFormEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)}
    (a : Γ ⊢ A ≡ A' type) (a_1 : (Γ ⬝ A) ⊢ B ≡ B' type),
    motive_4 Γ A A' a → motive_4 (Γ ⬝ A) B B' a_1
    → motive_4 Γ (A.pi B) (A'.pi B') (IsEqualType.pi_form_eq a a_1))
  → (IsEqualTypeSigmaFormEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)} 
    (a : Γ ⊢ A ≡ A' type) (a_1 : (Γ ⬝ A) ⊢ B ≡ B' type),
    motive_4 Γ A A' a → motive_4 (Γ ⬝ A) B B' a_1 
    → motive_4 Γ (A.sigma B) (A'.sigma B') (IsEqualType.sigma_form_eq a a_1))
  → (IsEqualTypeIdenFormEq : ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ : Tm n} 
    (a : Γ ⊢ a₁ ≡ a₂ ∶ A) (a_1 : Γ ⊢ a₃ ≡ a₄ ∶ A),
    motive_5 Γ a₁ a₂ A a → motive_5 Γ a₃ a₄ A a_1 
    → motive_4 Γ (A.iden a₁ a₃) (A.iden a₂ a₄) (IsEqualType.iden_form_eq a a_1))
  → (IsEqualTypeUnivFormEq : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_4 Γ U U (IsEqualType.univ_form_eq a))
  → (IsEqualTypeUnivElimEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} 
    (a : Γ ⊢ A ≡ A' ∶ U), motive_5 Γ A A' U a → motive_4 Γ A A' (IsEqualType.univ_elim_eq a))
  → (IsEqualTermVarEq : ∀ {x : Nat} {Γ : Ctx x} {A : Tm x} 
    (a : Γ ⊢ A type), motive_2 Γ A a 
    → motive_5 (Γ ⬝ A) v(0) v(0) (weaken A Weak.id.shift) (IsEqualTerm.var_eq a))
  → (IsEqualTermUnitComp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n} 
    (a_1 : (Γ ⬝ 𝟙) ⊢ A type) (a_2 : Γ ⊢ a ∶ substitute_zero A ⋆),
    motive_2 (Γ ⬝ 𝟙) A a_1 → motive_3 Γ a (substitute_zero A ⋆) a_2 
    → motive_5 Γ (A.indUnit ⋆ a) a (substitute_zero A ⋆) (IsEqualTerm.unit_comp a_1 a_2))
  → (IsEqualTermPiComp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n} 
    (a_1 : (Γ ⬝ A) ⊢ b ∶ B) (a_2 : Γ ⊢ a ∶ A), motive_3 (Γ ⬝ A) b B a_1 → motive_3 Γ a A a_2 
    → motive_5 Γ ((A.lam b).app a) (substitute_zero b a) (substitute_zero B a) 
      (IsEqualTerm.pi_comp a_1 a_2))
  → (IsEqualTermSigmaComp : ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} 
    {c : Tm (n + 1 + 1)} (a_1 : Γ ⊢ a ∶ A)
    (a_2 : Γ ⊢ b ∶ substitute_zero B a) (a_3 : (Γ ⬝ A.sigma B) ⊢ C type)
    (a_4 : (Γ ⬝ A ⬝ B) ⊢ c ∶ substitute C (Subst.weak Weak.id.shift.shift, v(1).pairSigma v(0))),
    motive_3 Γ a A a_1 → motive_3 Γ b (substitute_zero B a) a_2 → motive_2 (Γ ⬝ A.sigma B) C a_3 
    → motive_3 (Γ ⬝ A ⬝ B) c (substitute C (Subst.weak Weak.id.shift.shift, v(1).pairSigma v(0))) a_4 
    → motive_5 Γ (A.indSigma B C c (a.pairSigma b)) (substitute c (Subst.weak Weak.id, a, b))
      (substitute_zero C (a.pairSigma b)) (IsEqualTerm.sigma_comp a_1 a_2 a_3 a_4))
  → (IsEqualTermIdenComp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} 
    {b : Tm n} {a : Tm n}
    (a_1 : (Γ ⬝ A ⬝ weaken A Weak.id.shift ⬝ (weaken A Weak.id.shift.shift).iden v(1) v(0)) ⊢ B type)
    (a_2 : Γ ⊢ b ∶ substitute B (Subst.weak Weak.id, a, a, .refl A a))
    (a_3 : Γ ⊢ a ∶ A),
    motive_2 (Γ ⬝ A ⬝ weaken A Weak.id.shift ⬝ (weaken A Weak.id.shift.shift).iden v(1) v(0)) B a_1 
  -- → HasType Γ b
  --   (substitute B (.weak .id, a, a, (.refl A a)))
    → motive_3 Γ b
      (substitute B (Subst.weak Weak.id, a, a, .refl A a)) a_2 
    → motive_3 Γ a A a_3 
    → motive_5 Γ (A.j B b a a (A.refl a)) b
      (substitute B (Subst.weak Weak.id, a, a, A.refl a)) (IsEqualTerm.iden_comp a_1 a_2 a_3))
  → (IsEqualTermUnitIntroEq : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_5 Γ ⋆ ⋆ 𝟙 (IsEqualTerm.unit_intro_eq a))
  → (IsEqualTermUnitElimEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n} 
    (a_1 : (Γ ⬝ 𝟙) ⊢ A ≡ A' type) (a_2 : Γ ⊢ a ≡ a' ∶ substitute_zero A ⋆) (a_3 : Γ ⊢ b ≡ b' ∶ 𝟙),
    motive_4 (Γ ⬝ 𝟙) A A' a_1 → motive_5 Γ a a' (substitute_zero A ⋆) a_2 → motive_5 Γ b b' 𝟙 a_3 
    → motive_5 Γ (A.indUnit b a) (A'.indUnit b' a') (substitute_zero A b) 
      (IsEqualTerm.unit_elim_eq a_1 a_2 a_3))
  → (IsEqualTermEmptyElimEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n} 
    (a : (Γ ⬝ 𝟘) ⊢ A ≡ A' type) (a_1 : Γ ⊢ b ≡ b' ∶ 𝟘), motive_4 (Γ ⬝ 𝟘) A A' a → motive_5 Γ b b' 𝟘 a_1 
    → motive_5 Γ (A.indEmpty b) (A'.indEmpty b') (substitute_zero A b) (IsEqualTerm.empty_elim_eq a a_1))
  → (IsEqualTermPiIntroEq : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b b' B : Tm (n + 1)} {A' : Tm n} 
    (a : (Γ ⬝ A) ⊢ b ≡ b' ∶ B), motive_5 (Γ ⬝ A) b b' B a 
    → motive_5 Γ (A.lam b) (A'.lam b') (A.pi B) (IsEqualTerm.pi_intro_eq a))
  → (IsEqualTermPiElimEq : ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n} 
    (a_1 : Γ ⊢ f ≡ f' ∶ A.pi B) (a_2 : Γ ⊢ a ≡ a' ∶ A), motive_5 Γ f f' (A.pi B) a_1 
    → motive_5 Γ a a' A a_2 → motive_5 Γ (f.app a) (f'.app a') (substitute_zero B a) 
      (IsEqualTerm.pi_elim_eq a_1 a_2))
  → (IsEqualTermSigmaIntroEq : ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)} 
    (a_1 : Γ ⊢ a ≡ a' ∶ A) (a_2 : Γ ⊢ b ≡ b' ∶ substitute_zero B a), motive_5 Γ a a' A a_1 
    → motive_5 Γ b b' (substitute_zero B a) a_2 
    → motive_5 Γ (a.pairSigma b) (a'.pairSigma b') (A.sigma B) (IsEqualTerm.sigma_intro_eq a_1 a_2))
  → (IsEqualTermSigmaElimEq :  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} 
    {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)} {c c' : Tm (n + 1 + 1)} 
    (a : Γ ⊢ A.sigma B ≡ A'.sigma B' type) (a_1 : Γ ⊢ p ≡ p' ∶ A.sigma B)
    (a_2 : (Γ ⬝ A.sigma B) ⊢ C ≡ C' type)
    (a_3 : (Γ ⬝ A ⬝ B) ⊢ c ≡ c' ∶ substitute C (Subst.weak Weak.id.shift.shift, v(1).pairSigma v(0))),
    motive_4 Γ (A.sigma B) (A'.sigma B') a → motive_5 Γ p p' (A.sigma B) a_1 
    → motive_4 (Γ ⬝ A.sigma B) C C' a_2 
    → motive_5 (Γ ⬝ A ⬝ B) c c' (substitute C (Subst.weak Weak.id.shift.shift, v(1).pairSigma v(0))) a_3 
    → motive_5 Γ (A.indSigma B C c p) (A'.indSigma B' C' c' p') (substitute_zero C p)
      (IsEqualTerm.sigma_elim_eq a a_1 a_2 a_3))
  → (IsEqualTermIdenIntroEq : ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n} 
    (a_1 : Γ ⊢ A ≡ A' type) (a_2 : Γ ⊢ a ≡ a' ∶ A), motive_4 Γ A A' a_1 → motive_5 Γ a a' A a_2 
    → motive_5 Γ (A.refl a) (A'.refl a') (A.iden a a) (IsEqualTerm.iden_intro_eq a_1 a_2))
  → (IsEqualTermIdenElimEq : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} 
    {b b' : Tm n} {a₁ a₃ A' a₂ a₄ p p' : Tm n}
    (a : (Γ ⬝ A ⬝ weaken A Weak.id.shift ⬝ (weaken A Weak.id.shift.shift).iden v(1) v(0)) ⊢ B ≡ B' type)
  -- → IsEqualTerm Γ b b' (substitute B (.weak .id, a₁, a₃, p))
    (a_1 : Γ ⊢ b ≡ b' ∶ substitute B (Subst.weak Weak.id, a₁, a₃, p))
    (a_2 : Γ ⊢ A.iden a₁ a₃ ≡ A'.iden a₂ a₄ type) (a_3 : Γ ⊢ p ≡ p' ∶ A.iden a₁ a₃),
    motive_4 (Γ ⬝ A ⬝ weaken A Weak.id.shift ⬝ (weaken A Weak.id.shift.shift).iden v(1) v(0)) B B' a 
    → motive_5 Γ b b' 
      (substitute B (Subst.weak Weak.id, a₁, a₃, p)) a_1
    → motive_4 Γ (A.iden a₁ a₃) (A'.iden a₂ a₄) a_2 → motive_5 Γ p p' (A.iden a₁ a₃) a_3 
    → motive_5 Γ (A.j B b a₁ a₃ p) (A'.j B' b' a₂ a₄ p') (substitute B (Subst.weak Weak.id, a₁, a₃, p))
      (IsEqualTerm.iden_elim_eq a a_1 a_2 a_3))
  → (IsEqualTermUnivUnitEq : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_5 Γ 𝟙 𝟙 U (IsEqualTerm.univ_unit_eq a))
  → (IsEqualTermUnivEmptyEq : ∀ {n : Nat} {Γ : Ctx n} 
    (a : Γ ctx), motive_1 Γ a → motive_5 Γ 𝟘 𝟘 U (IsEqualTerm.univ_empty_eq a))
  → (IsEqualTermUnivPiEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)} 
    (a : Γ ⊢ A ≡ A' ∶ U) (a_1 : (Γ ⬝ A) ⊢ B ≡ B' ∶ U), motive_5 Γ A A' U a 
    → motive_5 (Γ ⬝ A) B B' U a_1 → motive_5 Γ (A.pi B) (A'.pi B') U (IsEqualTerm.univ_pi_eq a a_1))
  → (IsEqualTermUnivSigmaEq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)} 
    (a : Γ ⊢ A ≡ A' ∶ U) (a_1 : (Γ ⬝ A) ⊢ B ≡ B' ∶ U), motive_5 Γ A A' U a →
    motive_5 (Γ ⬝ A) B B' U a_1 
    → motive_5 Γ (A.sigma B) (A'.sigma B') U (IsEqualTerm.univ_sigma_eq a a_1))
  → (IsEqualTermUnivIdenEq : ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n} 
    (a : Γ ⊢ A ≡ A' ∶ U) (a_1 : Γ ⊢ a₁ ≡ a₂ ∶ A) (a_2 : Γ ⊢ a₃ ≡ a₄ ∶ A), motive_5 Γ A A' U a 
    → motive_5 Γ a₁ a₂ A a_1 → motive_5 Γ a₃ a₄ A a_2 
    → motive_5 Γ (A.iden a₁ a₃) (A'.iden a₂ a₄) U (IsEqualTerm.univ_iden_eq a a_1 a_2))
  → (IsEqualTermTyConvEq : ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n} 
    (a_1 : Γ ⊢ a ≡ b ∶ A) (a_2 : Γ ⊢ A ≡ B type), motive_5 Γ a b A a_1 → motive_4 Γ A B a_2 
    → motive_5 Γ a b B (IsEqualTerm.ty_conv_eq a_1 a_2))
  →
  -- result
  (∀ {n : Nat} {Γ : Ctx n}, (isCtx : IsCtx Γ) → motive_1 Γ isCtx)
  ∧ (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, (isType : IsType Γ A) → motive_2 Γ A isType)
  ∧ (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (hasType : HasType Γ a A) → motive_3 Γ a A hasType)
  ∧ (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    (isEqualType : IsEqualType Γ A A') → motive_4 Γ A A' isEqualType)
  ∧ (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (isEqualTerm : IsEqualTerm Γ a a' A) → motive_5 Γ a a' A isEqualTerm) :=
  by
    intro motive_1 motive_2 motive_3 motive_4 motive_5
    intro hIsCtxEmpty hIsCtxExtend
    intro hIsTypeUnitForm hIsTypeEmptyForm hIsTypePiForm hIsTypeSigmaForm hIsTypeIdenForm 
          hIsTypeUnivForm hIsTypeUnivElim
    intro hHasTypeVar hHasTypeUnitIntro hHasTypePiIntro hHasTypeSigmaIntro hHasTypeIdenIntro
          hHasTypeUnivUnit hHasTypeUnivEmpty hHasTypeUnivPi hHasTypeUnivSigma hHasTypeUnivIden
          hHasTypeUnitElim hHasTypeEmptyElim hHasTypePiElim hHasTypeSigmaElim hHasTypeIdenElim
          hHasTypeTyConv
    intro hIsEqualTypeUnitFormEq hIsEqualTypeEmptyFormEQ hIsEqualTypePiFormEq hIsEqualTypeSigmaFormEq
          hIsEqualTypeIdenFormEq hIsEqalTypeUnivFormEq hIsEqualTypeUnivElimEq
    intro hIsEqualTermVarEq hIsEqualTermUnitComp hIsEqualTermPiComp hIsEqualTermSigmaComp
          hIsEqualTermIdenComp hIsEqualTermUnitIntroEq hIsEqualTermUnitElimEq hIsEqualTermEmptyElimEq
          hIsEqualTermPiIntroEq hIsEqualTermPiElimEq hIsEqualTermSigmaIntroEq hIsEqualTermSigmaElimEq
          hIsEqualTermIdenIntroEq hIsEqualTermIdenElimEq hIsEqualTermUnivUnitEq hIsEqualTermUnivEmptyEq
          hIsEqualTermUnivPiEq hIsEqualTermUnivSigmaEq hIsEqualTermUnivIdenEq hIsEqualTermTyConvEq
    any_goals repeat' apply And.intro
    · intro n Γ isCtx
      apply IsCtx.recOn
        (motive_1 := motive_1) (motive_2 := motive_2) (motive_3 := motive_3) 
        (motive_4 := motive_4) (motive_5 := motive_5)
        isCtx
        hIsCtxEmpty hIsCtxExtend
        hIsTypeUnitForm hIsTypeEmptyForm hIsTypePiForm hIsTypeSigmaForm hIsTypeIdenForm
          hIsTypeUnivForm hIsTypeUnivElim
        hHasTypeVar hHasTypeUnitIntro hHasTypePiIntro hHasTypeSigmaIntro hHasTypeIdenIntro
          hHasTypeUnivUnit hHasTypeUnivEmpty hHasTypeUnivPi hHasTypeUnivSigma hHasTypeUnivIden
          hHasTypeUnitElim hHasTypeEmptyElim hHasTypePiElim hHasTypeSigmaElim hHasTypeIdenElim
          hHasTypeTyConv
        hIsEqualTypeUnitFormEq hIsEqualTypeEmptyFormEQ hIsEqualTypePiFormEq hIsEqualTypeSigmaFormEq
          hIsEqualTypeIdenFormEq hIsEqalTypeUnivFormEq hIsEqualTypeUnivElimEq
        hIsEqualTermVarEq hIsEqualTermUnitComp hIsEqualTermPiComp hIsEqualTermSigmaComp
          hIsEqualTermIdenComp hIsEqualTermUnitIntroEq hIsEqualTermUnitElimEq hIsEqualTermEmptyElimEq
          hIsEqualTermPiIntroEq hIsEqualTermPiElimEq hIsEqualTermSigmaIntroEq hIsEqualTermSigmaElimEq
          hIsEqualTermIdenIntroEq hIsEqualTermIdenElimEq hIsEqualTermUnivUnitEq hIsEqualTermUnivEmptyEq
          hIsEqualTermUnivPiEq hIsEqualTermUnivSigmaEq hIsEqualTermUnivIdenEq hIsEqualTermTyConvEq
    · intro n Γ A isType
      apply IsType.recOn
        (motive_1 := motive_1) (motive_2 := motive_2) (motive_3 := motive_3) 
        (motive_4 := motive_4) (motive_5 := motive_5)
        isType
        hIsCtxEmpty hIsCtxExtend
        hIsTypeUnitForm hIsTypeEmptyForm hIsTypePiForm hIsTypeSigmaForm hIsTypeIdenForm
          hIsTypeUnivForm hIsTypeUnivElim
        hHasTypeVar hHasTypeUnitIntro hHasTypePiIntro hHasTypeSigmaIntro hHasTypeIdenIntro
          hHasTypeUnivUnit hHasTypeUnivEmpty hHasTypeUnivPi hHasTypeUnivSigma hHasTypeUnivIden
          hHasTypeUnitElim hHasTypeEmptyElim hHasTypePiElim hHasTypeSigmaElim hHasTypeIdenElim
          hHasTypeTyConv
        hIsEqualTypeUnitFormEq hIsEqualTypeEmptyFormEQ hIsEqualTypePiFormEq hIsEqualTypeSigmaFormEq
          hIsEqualTypeIdenFormEq hIsEqalTypeUnivFormEq hIsEqualTypeUnivElimEq
        hIsEqualTermVarEq hIsEqualTermUnitComp hIsEqualTermPiComp hIsEqualTermSigmaComp
          hIsEqualTermIdenComp hIsEqualTermUnitIntroEq hIsEqualTermUnitElimEq hIsEqualTermEmptyElimEq
          hIsEqualTermPiIntroEq hIsEqualTermPiElimEq hIsEqualTermSigmaIntroEq hIsEqualTermSigmaElimEq
          hIsEqualTermIdenIntroEq hIsEqualTermIdenElimEq hIsEqualTermUnivUnitEq hIsEqualTermUnivEmptyEq
          hIsEqualTermUnivPiEq hIsEqualTermUnivSigmaEq hIsEqualTermUnivIdenEq hIsEqualTermTyConvEq
    · intro n Γ a A hasType
      apply HasType.recOn
        (motive_1 := motive_1) (motive_2 := motive_2) (motive_3 := motive_3) 
        (motive_4 := motive_4) (motive_5 := motive_5)
        hasType
        hIsCtxEmpty hIsCtxExtend
        hIsTypeUnitForm hIsTypeEmptyForm hIsTypePiForm hIsTypeSigmaForm hIsTypeIdenForm
          hIsTypeUnivForm hIsTypeUnivElim
        hHasTypeVar hHasTypeUnitIntro hHasTypePiIntro hHasTypeSigmaIntro hHasTypeIdenIntro
          hHasTypeUnivUnit hHasTypeUnivEmpty hHasTypeUnivPi hHasTypeUnivSigma hHasTypeUnivIden
          hHasTypeUnitElim hHasTypeEmptyElim hHasTypePiElim hHasTypeSigmaElim hHasTypeIdenElim
          hHasTypeTyConv
        hIsEqualTypeUnitFormEq hIsEqualTypeEmptyFormEQ hIsEqualTypePiFormEq hIsEqualTypeSigmaFormEq
          hIsEqualTypeIdenFormEq hIsEqalTypeUnivFormEq hIsEqualTypeUnivElimEq
        hIsEqualTermVarEq hIsEqualTermUnitComp hIsEqualTermPiComp hIsEqualTermSigmaComp
          hIsEqualTermIdenComp hIsEqualTermUnitIntroEq hIsEqualTermUnitElimEq hIsEqualTermEmptyElimEq
          hIsEqualTermPiIntroEq hIsEqualTermPiElimEq hIsEqualTermSigmaIntroEq hIsEqualTermSigmaElimEq
          hIsEqualTermIdenIntroEq hIsEqualTermIdenElimEq hIsEqualTermUnivUnitEq hIsEqualTermUnivEmptyEq
          hIsEqualTermUnivPiEq hIsEqualTermUnivSigmaEq hIsEqualTermUnivIdenEq hIsEqualTermTyConvEq
    · intro n Γ A A' isEqualType
      apply IsEqualType.recOn
        (motive_1 := motive_1) (motive_2 := motive_2) (motive_3 := motive_3) 
        (motive_4 := motive_4) (motive_5 := motive_5)
        isEqualType
        hIsCtxEmpty hIsCtxExtend
        hIsTypeUnitForm hIsTypeEmptyForm hIsTypePiForm hIsTypeSigmaForm hIsTypeIdenForm
          hIsTypeUnivForm hIsTypeUnivElim
        hHasTypeVar hHasTypeUnitIntro hHasTypePiIntro hHasTypeSigmaIntro hHasTypeIdenIntro
          hHasTypeUnivUnit hHasTypeUnivEmpty hHasTypeUnivPi hHasTypeUnivSigma hHasTypeUnivIden
          hHasTypeUnitElim hHasTypeEmptyElim hHasTypePiElim hHasTypeSigmaElim hHasTypeIdenElim
          hHasTypeTyConv
        hIsEqualTypeUnitFormEq hIsEqualTypeEmptyFormEQ hIsEqualTypePiFormEq hIsEqualTypeSigmaFormEq
          hIsEqualTypeIdenFormEq hIsEqalTypeUnivFormEq hIsEqualTypeUnivElimEq
        hIsEqualTermVarEq hIsEqualTermUnitComp hIsEqualTermPiComp hIsEqualTermSigmaComp
          hIsEqualTermIdenComp hIsEqualTermUnitIntroEq hIsEqualTermUnitElimEq hIsEqualTermEmptyElimEq
          hIsEqualTermPiIntroEq hIsEqualTermPiElimEq hIsEqualTermSigmaIntroEq hIsEqualTermSigmaElimEq
          hIsEqualTermIdenIntroEq hIsEqualTermIdenElimEq hIsEqualTermUnivUnitEq hIsEqualTermUnivEmptyEq
          hIsEqualTermUnivPiEq hIsEqualTermUnivSigmaEq hIsEqualTermUnivIdenEq hIsEqualTermTyConvEq
    · intro n Γ a a' A isEqualTerm
      apply IsEqualTerm.recOn
        (motive_1 := motive_1) (motive_2 := motive_2) (motive_3 := motive_3) 
        (motive_4 := motive_4) (motive_5 := motive_5)
        isEqualTerm
        hIsCtxEmpty hIsCtxExtend
        hIsTypeUnitForm hIsTypeEmptyForm hIsTypePiForm hIsTypeSigmaForm hIsTypeIdenForm
          hIsTypeUnivForm hIsTypeUnivElim
        hHasTypeVar hHasTypeUnitIntro hHasTypePiIntro hHasTypeSigmaIntro hHasTypeIdenIntro
          hHasTypeUnivUnit hHasTypeUnivEmpty hHasTypeUnivPi hHasTypeUnivSigma hHasTypeUnivIden
          hHasTypeUnitElim hHasTypeEmptyElim hHasTypePiElim hHasTypeSigmaElim hHasTypeIdenElim
          hHasTypeTyConv
        hIsEqualTypeUnitFormEq hIsEqualTypeEmptyFormEQ hIsEqualTypePiFormEq hIsEqualTypeSigmaFormEq
          hIsEqualTypeIdenFormEq hIsEqalTypeUnivFormEq hIsEqualTypeUnivElimEq
        hIsEqualTermVarEq hIsEqualTermUnitComp hIsEqualTermPiComp hIsEqualTermSigmaComp
          hIsEqualTermIdenComp hIsEqualTermUnitIntroEq hIsEqualTermUnitElimEq hIsEqualTermEmptyElimEq
          hIsEqualTermPiIntroEq hIsEqualTermPiElimEq hIsEqualTermSigmaIntroEq hIsEqualTermSigmaElimEq
          hIsEqualTermIdenIntroEq hIsEqualTermIdenElimEq hIsEqualTermUnivUnitEq hIsEqualTermUnivEmptyEq
          hIsEqualTermUnivPiEq hIsEqualTermUnivSigmaEq hIsEqualTermUnivIdenEq hIsEqualTermTyConvEq
