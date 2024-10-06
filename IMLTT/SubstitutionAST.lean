import IMLTT.AbstractSyntax

-- ASTs

inductive Adj where
  | shift : Adj
  | lift : Adj

inductive Weak where
  | id : Weak
  | mod : Adj →  Weak → Weak

inductive Subst where
  | weak : Weak → Subst
  | shift : Subst → Subst
  | lift : Subst → Subst
  | ext : Subst → Tm → Subst

-- TODO: comp fehlt beim AST

-- AST → AST

-- TODO

-- AST → (Nat → Tm)

def id_subst : Nat → Tm :=
  .var

-- TODO: is this correct?
def shift (σ : Nat → Tm) : Nat → Tm
  | i => σ (i + 1)

def lift (σ : Nat → Tm) : Nat → Tm
   | 0 => σ 0
   | i + 1 => σ i

def weak_subst (ρ : Weak) : Nat → Tm :=
  match ρ with
  | .id => id_subst
  | .mod mod ρ => 
    match mod with
    | .shift => shift (weak_subst ρ)
    | .lift => shift (weak_subst ρ)

def extend (σ : Nat → Tm) (t : Tm) : Nat → Tm
  | 0 => t
  | (i + 1) => σ i

def subst_subst (σ : Subst) : Nat → Tm :=
  match σ with
  | .weak ρ => weak_subst ρ
  | .shift σ => shift (subst_subst σ)
  | .lift σ => lift (subst_subst σ)
  | .ext σ t => extend (subst_subst σ) t

-- TODO: change -> first do Tm → Subst → Tm, then for .var: (subst_subst σ) i
def sub (t : Tm) (σ : Nat → Tm) : Tm :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (sub A σ) (sub B (lift σ))
  | .sigma A B => .sigma (sub A σ) (sub B (lift σ))
  | .iden A a a' => .iden (sub A σ) (sub a σ) (sub a' σ)
  | .univ => .univ
  | .var i => σ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (sub A (lift σ)) (sub b σ) (sub a σ)
  | .indEmpty A b => .indEmpty (sub A (lift σ)) (sub b σ)
  | .lam A b => .lam (sub A σ) (sub b (lift σ))
  | .app f a => .app (sub f σ) (sub a σ)
  | .pairSigma a b => .pairSigma (sub a σ) (sub b (lift σ))
  | .indSigma A B C c p => .indSigma (sub A σ) (sub B (lift σ)) 
                            (sub C (lift σ)) (sub c (lift (lift σ)))
                            (sub p σ) -- FIXME: Σ-comp is wrong - last assumption
  | .refl A a => .refl (sub A σ) (sub a σ)
  | .j A B b a a' p => .j (sub A σ) (sub B (lift (lift (lift σ))))
                        (sub b (lift σ)) (sub a σ) (sub a' σ)
                        (sub p σ) -- FIXME: j-rule is wrong

def comp_subst (σ σ' : Nat → Tm) : Nat → Tm
  | i => sub (σ' i) σ
