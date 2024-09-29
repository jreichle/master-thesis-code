import IMLTT.AbstractSyntax 

-- FIXME: subsitute, lift in type annotations? e.g. in j

/- # Lifting -/
-- needed to preserver `original depth` of variables
-- -> free variables need to refer to same context entry or constant
-- currently according to Abel and colleagues (2007)
def lift (l j : Nat) : Tm -> Tm
  | .unit => .unit
  | .empty => .empty
  | .pi A B  => .pi (lift l j A) (lift (l + 1) j B)
  | .sigma A B => .sigma (lift l j A) (lift (l + 1) j B)
  | .iden A s t => .iden (lift l j A) (lift l j s) (lift l j t)
  | .univ => .univ
  | .var i =>
      if i < l
        then .var i
        else .var (i + j)
  | .tt => .tt
  | .indUnit A s t => .indUnit (lift l j A) (lift l j s) (lift l j t)
  | .indEmpty A s => .indEmpty (lift l j A) (lift l j s)
  | .lam s t => .lam (lift l j s) (lift (l + 1) j t)
  | .app s t => .app (lift l j s) (lift l j t)
  | .pairSigma s t => .pairSigma (lift l j s) (lift (l + 1) j t)
  | .indSigma A B C s t => .indSigma (lift l j A) (lift l j B) (lift l j C) 
                            (lift l j s) (lift l j t)
  | .refl A t => .refl (lift l j A) (lift l j t)
  | .j A B t a b p => .j (lift l j A) (lift l j B) (lift l j t) (lift l j a) (lift l j b) (lift l j p)

-- TODO: use more efficient lifting
-- - on λ-calculus (ex3) lecture only apply lifting when really substituted

/- # Substitution -/
-- lifting used
-- decrease var that references binder outside the length of the substitution
def substitute (s : Tm) (t : Tm) (j : Nat) : Tm :=
  match s with
  | .unit => .unit
  | .empty => .empty
  | .pi A B  => .pi (substitute A t j) (substitute B (lift 0 1 t) (j + 1))
  | .sigma A B => .sigma (substitute A t j) (substitute B (lift 0 1 t) (j + 1))
  | .iden A m n => .iden A (substitute m t j) (substitute n t j)
  | .univ => .univ
  | .var i =>
      if i < j
        then .var i
        else if i = j
          then t
          else .var (i - 1)
  | .tt => .tt
  | .indUnit A m n => .indUnit (substitute A t j) (substitute m t j) (substitute n t j)
  | .indEmpty A m => .indEmpty (substitute A t j) (substitute m t j)
  | .lam m n => .lam (substitute m t j) (substitute n (lift 0 1 t) (j + 1))
  | .app m n => .app (substitute m t j) (substitute n t j)
  | .pairSigma m n => .pairSigma (substitute m t j) (substitute n (lift 0 1 t) (j + 1))
  | .indSigma A B C m n => .indSigma (substitute A t j) (substitute B t j) (substitute C t j) 
                            (substitute m t j) (substitute n t j)
  | .refl A m => .refl (substitute A t j) (substitute m t j)
  | .j A B u a b p => .j (substitute A t j) (substitute B t j) (substitute u t j) (substitute a t j) 
                      (substitute b t j) (substitute p t j)

notation A "[" t  "/" j"]" => substitute A t j

def lift_ctx (l j : Nat) : Ctx -> Ctx
  | .empty => .empty
  | .extend Γ A => .extend (lift_ctx l j Γ) (lift l j A)
