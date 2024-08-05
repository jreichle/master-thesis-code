import IMLTT.AbstractSyntax
import IMLTT.Substitution

/- # Rules -/
-- 5 judgments:
-- - Γ ctx
-- - Γ ⊢ A type
-- - Γ ⊢ a : A
-- - Γ ⊢ A = A' type
-- - Γ ⊢ a = a' : A

mutual
  -- Γ ctx
  inductive IsCtx : Ctx → Prop where
    | empty : IsCtx Ctx.empty
    | extend : IsCtx Γ → IsType Γ A → IsCtx (Γ ⬝ A)

  -- Γ ⊢ A type
  inductive IsType : Ctx → Tm → Prop where
    -- formation rules
    | unit_form : IsCtx Γ
                  → IsType Γ ⊤
    | empty_form : IsCtx Γ
                   → IsType Γ ⊥
    | pi_form : IsType Γ A → IsType (Γ ⬝ A) B
                → IsType Γ (Tm.pi A B)
    | sigma_form : IsType Γ A → IsType (Γ ⬝ A) B
                   → IsType Γ (Tm.sigma A B)
    | iden_form : IsType Γ A
                  → IsType ((Γ ⬝ A) ⬝ A) (Tm.iden A 1 0)
    | univ_form : IsType Γ U
    | univ_elim : HasType Γ A U → IsType Γ A

  -- Γ ⊢ a : A
  inductive HasType : Ctx → Tm → Tm → Prop where
    -- structural rules -- make sure v_0 of A doesn't refer to A itself
    | var  : IsType Γ A
             → HasType (Γ ⬝ A) 0 (lift 0 1 A) 
    | weak : HasType Γ (Tm.var i) A → IsType Γ B
             → HasType (Γ ⬝ B) (Tm.var (i + 1)) (lift 0 1 A)
    -- intro rules
    | unit_intro : IsCtx Γ
                   → HasType Γ tt ⊤
    | pi_intro : HasType (Γ ⬝ A) b B
                 → HasType Γ (Tm.lam b) (Tm.pi A B)
    | sigma_intro : HasType Γ a A → HasType Γ b (substitute B a 0)
                    → HasType Γ (Tm.pairSigma a b) (Tm.sigma A B)
    | iden_intro : IsType Γ A
                   → HasType (Γ ⬝ A) (Tm.refl 0) (Tm.iden A 0 0)
    -- universe intro
    | univ_unit : IsCtx Γ
                  → HasType Γ ⊤ U
    | univ_empty : IsCtx Γ →
                   HasType Γ ⊥ U
    | univ_pi : HasType Γ A U → HasType (Γ ⬝ A) B U
                → HasType Γ (Tm.pi A B) U
    | univ_sigma : HasType Γ A U → HasType (Γ ⬝ A) B U
                 → HasType Γ (Tm.sigma A B) U
    | univ_iden : HasType Γ A U
                  → HasType ((Γ ⬝ A) ⬝ A) (Tm.iden A 0 1) U
    -- elimination rules (except univ)
    | unit_elim : IsType (Γ ⬝ Tm.unit) C → HasType Γ c (substitute C Tm.unit 0) → HasType Γ p Tm.unit
                  → HasType Γ (Tm.indUnit p c) (substitute C p 0)
    | empty_elim : IsType (Γ ⬝ ⊥) C → HasType Γ p ⊥
                   → HasType Γ (Tm.indEmpty p) (substitute C p 0)
    | pi_elim : HasType Γ f (Tm.pi A B) → HasType Γ a A
                → HasType Γ (Tm.app f a) (substitute B A 0)
    | sigma_elim₁ : HasType Γ z (Tm.sigma A B)
                    → HasType Γ (Tm.prjSigma₁ z) A
    | sigma_elim₂ : HasType Γ z (Tm.sigma A B)
                    → HasType Γ (Tm.prjSigma₂ z) (substitute B (Tm.prjSigma₁ z) 0)
    | iden_elim : IsType (((Γ ⬝ A) ⬝ A) ⬝ (Tm.iden A a b)) C
                  → HasType (Γ ⬝ A) t
                      (substitute (substitute (substitute C 0 2) 0 1) (Tm.refl 0) 0)
                  → HasType (((Γ ⬝ A) ⬝ A) ⬝ (Tm.iden A 2 1)) (Tm.j t 2 1 0) C

    -- pi_Σ₁
    -- pi_+₁
  -- Γ ⊢ A ≡ B type
  inductive IsEqualType : Ctx → Tm → Tm → Prop where

  -- Γ ⊢ a ≡ b : A
  inductive IsEqualTerm : Ctx → Tm → Tm → Tm → Prop where
    -- computation rules
    | unit_comp : IsType (Γ ⬝ ⊤) C → HasType Γ c (substitute C Tm.tt 0)
                  → IsEqualTerm Γ (Tm.indUnit Tm.tt c) Tm.tt (substitute C Tm.tt 0)
    | pi_comp : HasType (Γ ⬝ A) b B → HasType Γ a A
                → IsEqualTerm Γ (Tm.app (Tm.lam b) a) (substitute b a 0) (substitute B a 0)
    | iden_comp : IsType (((Γ ⬝ A) ⬝ A) ⬝ (Tm.iden A a b)) C
                  → HasType (Γ ⬝ A) t (substitute (substitute (substitute C 0 2) 0 1)
                      (Tm.refl 0) 0)
                  → IsEqualTerm (Γ ⬝ A) (Tm.j t 0 0 (Tm.refl 0)) t
                      (substitute (substitute (substitute C 0 2) 0 1) (Tm.refl 0) 0)
    | sigma_comp₁ : HasType Γ a A → HasType Γ b (substitute B a 0)
                    → IsEqualTerm Γ (Tm.prjSigma₁ (Tm.pairSigma a b)) a A
    | sigma_comp₂ : HasType Γ a A → HasType Γ b (substitute B a 0)
                    → IsEqualTerm Γ (Tm.prjSigma₂ (Tm.pairSigma a b)) b
                      (substitute B (Tm.prjSigma₁ (Tm.pairSigma a b)) 0)
end

postfix : max " ctx" => IsCtx
notation Γ " ⊢ " A  " type" => IsType Γ A
notation Γ " ⊢ " s " ∶ " A => HasType Γ s A
notation Γ " ⊢ " A " ≡ " B => IsEqualType Γ A B
notation Γ " ⊢ " s " ≡ " t " ∶ " A => IsEqualTerm Γ s t A
