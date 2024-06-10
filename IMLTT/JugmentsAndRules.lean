import IMLTT.AbstractSyntax

/- # Rules - judgments implicitly in rules -/
-- 5 judgments:
-- - Γ ctx
-- - Γ ⊢ A type
-- - Γ ⊢ A = A' type
-- - Γ ⊢ a : A
-- - Γ ⊢ a = a' : A

-- FIXME: is it not importatnt that ⊢ (Γ, σ) ctx is checked in terms of context formation?
-- Type formers
inductive Form : Ctx → Tm → Prop where
  | unit : Form Γ ⊤
  | pi   : Form Γ σ → Form (Γ; σ) τ → Form Γ (Πσ, τ)
  | sum  : Form Γ σ → Form (Γ; σ) τ → Form Γ (Σσ, τ)
  | iden : Form Γ σ → Form (Γ; σ) τ → Form Γ (Tm.iden σ x y)
  | univ : Form Γ univ

notation : 10 Γ " ⊢ " T  " type" => Form Γ T

-- contexts formation
inductive CtxForm : Ctx → Prop where
  | nil : CtxForm nil
  | cons : CtxForm Γ → (Γ ⊢ A type) → CtxForm (Γ; A)

notation Γ " ctx" => CtxForm Γ

-- structural - var
inductive VarRule : Ctx → Tm → Prop where
  | var : Γ ⊢ T type → VarRule (Γ; T) T

-- TODO: is this weakening, var?
inductive VarHasType : Ctx → Nat → Tm → Prop where
  | zero : VarHasType (T :: Γ) 0 T
  | succ : VarHasType Γ n T → VarHasType (U :: Γ) (n + 1) T

notation : 10 Γ " ⊢ᵥ " n " ∶ " T => VarHasType Γ n T

-- definitional equality
-- - refl
-- - symm
-- - trans
-- - subs
-- - var conv

-- term formers
inductive Intro : Ctx → Tm → Tm → Prop where
  | var  : (Γ ⊢ᵥ n ∶ T) → Intro Γ (.var n) T
  | tt   : Intro Γ tt ⊤
  | lam  : Intro (σ :: Γ) t τ → Intro Γ (λ σ, t) (Πσ, τ)
  | pair : Intro Γ m σ → Intro Γ n τ → Intro Γ ⟨m, n⟩ (Σσ, τ) 
                         -- FIXME: add substitution to tau or add to context
  | refl : Intro Γ t σ → Intro Γ refl(t) (Tm.iden σ t t)
  -- FIXME: univ

notation : 10 Γ " ⊢ " t " ∶ " T => Intro Γ t T

inductive Weakening : Ctx → Tm → Tm → Prop where
  | weak : Intro (Δ ++ Γ) j J → (Γ ⊢ A type) → Weakening (Δ ++ (Γ; A)) j J

inductive Substitution : Ctx → Tm where
  | subst : Form (Γ; A) P → Intro Γ t A → Substitution Γ (sub P t n)


def type_check (Γ : Ctx) : (T : Tm) → Option (PLift (Γ ⊢ T type))
  | .unit => do sorry -- return ⟨Γ ⊢ ⊤ type⟩ -- TODO: needs to be proof
  | .pi σ τ => do sorry
  | .sum σ τ => do sorry
  | .iden σ m n => do sorry
  | .univ => do sorry
  | _  => do failure

def term_check (Γ : Ctx) : (t : Tm) → (T : Tm) → Option (PLift (Γ ⊢ t ∶ T)) :=
  sorry









