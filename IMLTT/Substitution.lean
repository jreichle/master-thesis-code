import IMLTT.AbstractSyntax

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
  | .indUnit s t => .indUnit (lift l j s) (lift l j t)
  | .indEmpty s => .indEmpty (lift l j s)
  | .lam s t => .lam (lift l j s) (lift (l + 1) j t)
  | .app s t => .app (lift l j s) (lift l j t)
  | .pairSigma s t => .pairSigma (lift l j s) (lift (l + 1) j t)
  | .indSigma s t => .indSigma (lift l j s) (lift l j t)
  | .refl t => .refl (lift l j t)
  | .j t a b p => .j (lift l j t) (lift l j a) (lift l j b) (lift l j p)

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
  | .indUnit m n => .indUnit (substitute m t j) (substitute n t j)
  | .indEmpty m => .indEmpty (substitute m t j)
  | .lam m n => .lam (substitute m t j) (substitute n (lift 0 1 t) (j + 1))
  | .app m n => .app (substitute m t j) (substitute n t j)
  | .pairSigma m n => .pairSigma (substitute m t j) (substitute n (lift 0 1 t) (j + 1))
  | .indSigma m n => .indSigma (substitute m t j) (substitute n t j)
  | .refl m => .refl (substitute m t j)
  | .j u a b p => .j (substitute u t j) (substitute a t j) (substitute b t j) (substitute p t j)
