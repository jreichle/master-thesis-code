import IMLTT.AbstractSyntax

-- TODO: use more efficient lifting (see e.g. van Benthem 1994 - Implementation LC or Dybier 2006 - NbE)

/-- lift term to avoid capturing free variables of substituted term during substitution -/
def lift (l : Nat) : Tm → Tm
  | .unit => .unit
  | .empty => .empty
  | .pi A B  => .pi (lift l A) (lift (l + 1) B)
  | .sigma A B => .sigma (lift l A) (lift (l + 1) B)
  | .iden A s t => .iden (lift l A) (lift l s) (lift l t)
  | .univ => .univ
  | .var i =>
      if i < l
        then .var i
        else .var (i + 1)
  | .tt => .tt
  | .indUnit s t => .indUnit (lift l s) (lift l t)
  | .indEmpty s => .indEmpty (lift l s)
  | .lam t => .lam (lift (l + 1) t)
  | .app s t => .app (lift l s) (lift l t)
  | .pairSigma s t => .pairSigma (lift l s) (lift (l + 1) t)
  | .prjSigma₁ s => .prjSigma₁ (lift l s)
  | .prjSigma₂ s => .prjSigma₂ (lift l s)
  | .refl t => .refl (lift l t)
  | .j t a b p => .j (lift l t) (lift l a) (lift l b) (lift l p)

def substitute (s : Tm) (t : Tm) (j : Nat) : Tm :=
  match s with
  | .unit => .unit
  | .empty => .empty
  | .pi A B  => .pi (substitute A t j) (substitute B (lift 0 t) (j + 1))
  | .sigma A B => .sigma (substitute A t j) (substitute B (lift 0 t) (j + 1))
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
  | .lam n => .lam (substitute n (lift 0 t) (j + 1))
  | .app m n => .app (substitute m t j) (substitute n t j)
  | .pairSigma m n => .pairSigma (substitute m t j) (substitute n (lift 0 t) (j + 1))
  | .prjSigma₁ m => .prjSigma₁ (substitute m t j)
  | .prjSigma₂ m => .prjSigma₂ (substitute m t j)
  | .refl m => .refl (substitute m t j)
  | .j u a b p => .j (substitute u t j) (substitute a t j) (substitute b t j) (substitute p t j)

def substitute_ctx (Γ : Ctx) (t : Tm) (j : Nat) : Ctx :=
  match Γ with
  | .empty => .empty
  | .extend Γ' A => (substitute_ctx Γ' t j) ⬝ (substitute A t j)
