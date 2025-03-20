inductive Tm : Nat → Type where
  -- 'types'
  | unit : Tm n
  | empty : Tm n
  | pi : Tm n → Tm (n + 1) → Tm n
  | sigma : Tm n → Tm (n + 1) → Tm n
  | nat : Tm n
  | iden : Tm n → Tm n → Tm n → Tm n
  | univ : Tm n
  -- 'terms'
  | var : Fin n → Tm n
  | tt : Tm n
  | indUnit : Tm (n + 1) → Tm n → Tm n → Tm n
  | indEmpty : Tm (n + 1) → Tm n → Tm n
  | lam : Tm n → Tm (n + 1) → Tm n
  | app : Tm n → Tm n → Tm n
  | pairSigma : Tm n → Tm n → Tm n
  | firstSigma : Tm n → Tm n
  | secondSigma : Tm n → Tm n
  | zeroNat : Tm n
  | succNat : Tm n → Tm n
  | indNat : Tm (n + 1) → Tm n → Tm (n + 2) → Tm n → Tm n
  | refl : Tm n → Tm n → Tm n
  | j : Tm n → Tm (n + 3) → Tm (n + 1) → Tm n → Tm n → Tm n → Tm n

inductive Ctx : Nat → Type where
  | empty : Ctx 0
  | extend : Ctx n → Tm n → Ctx (n + 1)

-- types
notation:max "𝟙" => Tm.unit
notation:max "𝟘" => Tm.empty
notation:98 "Π" A ";" B => Tm.pi A B
notation:98 "Σ" A ";" B => Tm.sigma A B
notation:max "𝒩" => Tm.nat
notation:98 s " ≃" "[" A "] " t => Tm.iden A s t
notation:max "𝒰" => Tm.univ
-- terms
notation:max "v(" x ")" => Tm.var x
notation:max "⋆" => Tm.tt
notation:98 "λ" A "; " b => Tm.lam A b
infixl:98 "◃" => Tm.app
infixl:98 "&" => Tm.pairSigma
prefix:98 "π₁" => Tm.firstSigma
prefix:98 "π₂" => Tm.secondSigma
notation:max "𝓏" => Tm.zeroNat -- 𝓏 𝓈
notation:max "𝓈(" x ")" => Tm.succNat x

notation:max "ε" => Ctx.empty
infixl:94 " ⬝ " => Ctx.extend

instance : Coe (Fin n) (Tm n) where
  coe n := .var n
