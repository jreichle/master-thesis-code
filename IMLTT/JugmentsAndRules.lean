import IMLTT.AbstractSyntax
import IMLTT.Substitution

/- # Rules - judgments implicitly in rules -/
-- 5 judgments:
-- - Γ ctx
-- - Γ ⊢ A type
-- - Γ ⊢ a : A
-- - Γ ⊢ A = A' type
-- - Γ ⊢ a = a' : A

class Judgment (a : Type)

mutual
  -- Γ ⊢ A type
  inductive IsType : Ctx → Tm → Prop where 
    -- form
    | unit : IsType Γ ⊤
    | pi   : IsType Γ A → IsType (Γ ⬝ A) B → IsType Γ (Tm.pi A B)
    | sum  : IsType Γ A → IsType (Γ ⬝ A) B → IsType Γ (Tm.sum A B)
    | iden : IsType Γ A → IsType (Γ ⬝ A) B → IsType Γ (Tm.iden A x y)
    | univ : IsType Γ univ -- FIXME: hierarchy?

  -- Γ ⊢ a : A
  inductive HasType : Ctx → Tm → Tm → Prop where
    -- intro
    | tt   : HasType Γ tt ⊤
    | lam  : HasType (Γ ⬝ A) t B → HasType Γ (Tm.lam A t) (Tm.pi A B)
    | pair : HasType Γ s A → HasType Γ t B → HasType Γ (Tm.pair s t) (Tm.sum A B)
    | refl : HasType Γ t A → HasType Γ (Tm.refl A t) (Tm.iden A t t)
    -- elim
    -- structural
    | var  : IsType Γ A → HasType (Γ ⬝ A) 0 A
    | weak : IsType Γ A → HasType Γ (Tm.var n) γ → HasType (Γ ⬝ A) (Tm.var (n + 1)) γ
      -- FIXME: not in correct form?

    inductive IsEqualType : Ctx → Tm → Tm → Prop where
      -- definitonal equality
      | rfl : IsType Γ A → IsEqualType Γ A A
      | sym : IsEqualType Γ A B → IsEqualType Γ B A
      | trns : IsEqualType Γ A B → IsEqualType Γ B C → IsEqualType Γ A C
      | subs : IsType Γ A → IsEqualTerm Γ a b A → IsType ((Γ ⬝ A), Δ) B
                → IsEqualType (Γ, (substitute_ctx  Δ b x))
                  (substitute B a x) (substitute B b x)
                -- FIXME: what's correct x?

    inductive IsEqualTerm : Ctx → Tm → Tm → Tm → Prop where
      -- definitonal equality
      | rfl : IsType Γ A → HasType Γ a A → IsEqualTerm Γ a a A
      | sym : IsEqualTerm Γ a b A → IsEqualTerm Γ b a A
      | trns : IsEqualTerm Γ a b A → IsEqualTerm Γ b c A → IsEqualTerm Γ a c A
      | subs : IsType Γ A → IsEqualTerm Γ a b A → HasType ((Γ ⬝ A), Δ) c B
                → IsEqualTerm (Γ, (substitute_ctx  Δ b x))
                  (substitute c a x) (substitute c b x) (substitute B b x)
                -- FIXME: what's correct x?
      -- comp
end

notation Γ " ⊢ " A  " type" => IsType Γ A
notation Γ " ⊢ " s " ∶ " A => HasType Γ s A
notation Γ " ⊢ " A " ≡ " B => IsEqualType Γ A B
notation Γ " ⊢ " s " ≡ " t " ∶ " A => IsEqualTerm Γ s t A

-- Γ ctx
inductive IsCtx : Ctx → Prop where
  | empty : IsCtx nil
  | extend : IsCtx Γ → IsType Γ A → IsCtx (Γ ⬝ A)

postfix : max " ctx" => IsCtx
