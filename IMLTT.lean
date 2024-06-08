import «IMLTT».Basic
import Aesop

-- FIXME: do!!
-- https://ncatlab.org/nlab/show/Martin-Löf+dependent+type+theory#presentation_1
-- https://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf
--
-- GITHUB project

/- # Abstract Syntax of MLTT -/

inductive Ty where
  | unit : Ty
  | pi   : Ty → Ty → Ty
  | sum  : Ty → Ty → Ty
  | iden : Ty → Tm → Tm → Ty
  | univ : Ty

-- FIXME: types and terms in same grammar

inductive Tm where
  | var  : Nat → Tm -- !!!de Bruijn!!!
  | tt   : Tm
  | lam  : Ty → Tm → Tm
  | pair : Tm → Tm → Tm
  | refl : Tm → Tm

notation "⊤" => Ty.unit
notation "Π" σ ", " τ => Ty.pi σ τ
notation "Σ" σ ", " τ => Ty.sum σ τ
notation "Id " σ " (" x ", "  y")" => Ty.iden σ x y -- might not want to use mixfix
notation "U" => Ty.univ -- FIXME:

notation "()" => Tm.tt
notation "λ " T ", " t => Tm.lam T t
notation "⟨" T ", " t "⟩" => Tm.pair T t
notation "refl(" t ")" => Tm.refl t

instance : Coe Nat Tm where
  coe := .var
instance : OfNat Tm n where
  ofNat := n

abbrev Ctx := List Ty
-- TODO: notation for empty context

/- # Rules - judgments implicitly -/

-- Contexts
-- TODO: empty context, cons

inductive CtxForm : Ctx → Prop where
  | nil : CtxForm nil

-- Variables
-- TODO: variable: var, weakening

inductive VarHasType : Ctx → Nat → Ty → Prop where
  | zero : VarHasType (T :: Γ) 0 T
  | succ : VarHasType Γ n T → VarHasType (U :: Γ) (n + 1) T

notation : 10 Γ " ⊢ᵥ " n " ∶ " T => VarHasType Γ n T

-- Type and Term rules --- Judgments are encoded implicitly
-- TODO: add substitution for types and terms?
-- TODO: Judements missing:
-- - Γ ⊢ A = A' type   (not derivable like in STLC)
-- - Γ ⊢ a = a' : A

-- Types
-- TODO mutual for form and type eq

inductive Form : Ctx → Ty → Prop where
  | unit : Form Γ ⊤
  | pi   : Form Γ σ → Form (σ :: Γ) τ → Form Γ (Πσ, τ)
  | sum  : Form Γ σ → Form (σ :: Γ) τ → Form Γ (Σσ, τ)
  | iden : Form Γ σ → Form (σ :: Γ) τ → Form Γ (Ty.iden σ x y)
                                     -- TODO:  (Id σ (x, y))
  | univ : ∀Γ : Ctx, Form Γ univ

notation : 10 Γ " ⊢ " T  " type" => Form Γ T

def type_check (Γ : Ctx) : (T : Ty) → Option (PLift (Γ ⊢ T type))
  | .unit => do return ⟨Γ ⊢ ⊤ type⟩ -- TODO: needs to be proof
  | .pi σ τ => do sorry
  | .sum σ τ => do sorry
  | .iden σ m n => do sorry
  | .univ => do sorry

-- Terms

inductive Intro : Ctx → Tm → Ty → Prop where
  | var  : (Γ ⊢ᵥ n ∶ T) → Intro Γ (.var n) T
  | tt   : Intro Γ tt ⊤
  | lam  : Intro (σ :: Γ) t τ → Intro Γ (λ σ, t) (Πσ, τ)
  | pair : Intro Γ m σ → Intro Γ n τ → Intro Γ ⟨m, n⟩ (Σσ, τ) -- FIXME: add substitution to tau or add to context
  | refl : Intro Γ t σ → Intro Γ refl(t) (Ty.iden σ t t) -- FIXME: iden, univ

notation : 10 Γ " ⊢ " t " ∶ " T => Intro Γ t T

def term_check (Γ : Ctx) : (t : Tm) → (T : Ty) → Option (PLift (Γ ⊢ t ∶ T)) :=
  sorry








-- TODO: add elimination and computation types and terms -> computation
-- - abs
-- - case
-- - j-rule?

