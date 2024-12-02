inductive Tm : Nat → Type where
  -- 'types'
  | unit : Tm n
  | empty : Tm n
  | pi : Tm n → Tm (n + 1) → Tm n
  | sigma : Tm n → Tm (n + 1) → Tm n
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
  | indSigma: Tm n → Tm (n + 1) → Tm (n + 1) → Tm (n + 2) → Tm n → Tm n
  | refl : Tm n → Tm n → Tm n
  | j : Tm n → Tm (n + 3) → Tm n → Tm n → Tm n → Tm n → Tm n

inductive Ctx : Nat → Type where
  | empty : Ctx 0
  | extend : Ctx n → Tm n → Ctx (n + 1)

-- types
notation "𝟙" => Tm.unit
notation "𝟘" => Tm.empty
notation:70 "Π" A ";" B => Tm.pi A B
notation:70 "Σ" A ";" B => Tm.sigma A B
notation:70 A "ℑ" s " ≃ " t => Tm.iden A s t -- FIXME:  do s =[A] t
notation "U" => Tm.univ
-- terms
notation:max "v(" x ")" => Tm.var x
notation "⋆" => Tm.tt
notation:70 "λ" A "; " b => Tm.lam A b
infixl : 70 "◃" => Tm.app
notation:70 a "&" b => Tm.pairSigma a b

instance : Coe (Fin n) (Tm n) where
  coe n := .var n

-- def convert_tm_higher (t : Tm m) (hleq : m ≤ n) : Tm n :=
--   sorry
-- 
-- theorem leq_add (m n : Nat) : m ≤ m + n :=
--   by
--     induction m with
--     | zero => simp []
--     | succ m' ih =>
--       rw [Nat.add_comm _ n]
--       rw [←Nat.add_assoc]
--       apply Nat.succ_le_succ
--       rw [Nat.add_comm]
--       apply ih
-- 
-- def concat_ctx (Γ : Ctx n) (Δ : Ctx m) : Ctx (n + m) :=
--   match Δ with
--   | .empty => Γ
--   | .extend Δ' A => .extend (concat_ctx Γ Δ') (convert_tm_higher A (by
--       simp []
--       rw [Nat.add_comm]
--       simp [leq_add])
--     )
-- infixl:65 "; " => concat_ctx

notation "ε" => Ctx.empty
infixl:66 " ⬝ " => Ctx.extend
