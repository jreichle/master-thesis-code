inductive Tm where
  -- 'types'
  | unit : Tm
  | empty : Tm
  | pi : Tm → Tm → Tm
  | sigma : Tm → Tm → Tm
  | iden : Tm → Tm → Tm → Tm
  | univ : Tm
  -- 'terms'
  | var : Nat → Tm
  | tt : Tm
  | indUnit : Tm → Tm → Tm → Tm
  | indEmpty : Tm → Tm → Tm
  | lam : Tm → Tm → Tm
  | app : Tm → Tm → Tm
  | pairSigma : Tm → Tm → Tm
  | indSigma: Tm → Tm → Tm → Tm → Tm → Tm
  | refl : Tm → Tm → Tm
  | j : Tm → Tm → Tm → Tm → Tm → Tm → Tm

-- types
notation "𝟙" => Tm.unit
notation "𝟘" => Tm.empty
notation "Π" A ", " B => Tm.pi A B
notation "Σ" A ", " B => Tm.sigma A B
notation "Id_" A " (" s ", " t")" => Tm.iden A s t
notation "U" => Tm.univ
-- terms
notation "()" => Tm.tt
notation "λ" s ", " t => Tm.lam s t
notation "<" A ", " s ">" => Tm.pair A s
notation "refl " A " (" s ")" => Tm.refl A s

instance : Coe Nat Tm where
  coe := .var
instance : OfNat Tm n where
  ofNat := n

inductive Ctx where
  | empty : Ctx
  | extend : Ctx → Tm → Ctx

def concat_ctx (Γ : Ctx) (Δ : Ctx) : Ctx :=
  match Δ with
  | .empty => Γ
  | .extend Δ' A => .extend (concat_ctx Γ Δ') A

def length_ctx (Γ : Ctx) : Nat :=
  match Γ with
  | .empty => 0
  | .extend Γ' _ => 1 + (length_ctx Γ')

notation "ε" => Ctx.empty
infixl:66 " ⬝ " => Ctx.extend
infixl:65 ", " => concat_ctx
