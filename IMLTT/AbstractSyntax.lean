inductive Tm where
  -- 'types'
  | unit : Tm
  | pi   : Tm → Tm → Tm
  | sum  : Tm → Tm → Tm
  | iden : Tm → Tm → Tm → Tm
  | univ : Tm -- add nat universe hierarchy
  -- 'terms'
  | var  : Nat → Tm -- !!!de Bruijn!!!
  | tt   : Tm
  | lam  : Tm → Tm → Tm
  | app  : Tm → Tm → Tm
  | pair : Tm → Tm → Tm
  | prj₁ : Tm → Tm
  | prj₂ : Tm → Tm
  | refl : Tm → Tm → Tm

inductive Ctx where
  | empty : Ctx
  | extend : Ctx → Tm → Ctx

def concat_ctx (Γ : Ctx) (Δ : Ctx) : Ctx :=
  match Δ with
  | Ctx.empty => Γ
  | Ctx.extend Δ' A => Ctx.extend (concat_ctx Γ Δ') A

def length_ctx (Γ : Ctx) : Nat :=
  match Γ with
  | Ctx.empty => 0
  | Ctx.extend Γ' _ => 1 + (length_ctx Γ')

infixl:65 " ⬝ " => Ctx.extend
infixl:65 ", " => concat_ctx

-- types
notation "⊤" => Tm.unit
notation "Π" A ", " B => Tm.pi A B
notation "Σ" A ", " B => Tm.sum A B
notation "Id " A " (" s ", " t")" => Tm.iden A s t
-- terms
notation "()" => Tm.tt
notation "λ " A ", " s => Tm.lam A s
notation "<" A ", " s ">" => Tm.pair A s
notation "refl " A " (" s ")" => Tm.refl A s

instance : Coe Nat Tm where
  coe := .var
instance : OfNat Tm n where
  ofNat := n
