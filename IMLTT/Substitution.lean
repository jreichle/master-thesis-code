import IMLTT.AbstractSyntax

-- lift term to avoid capturing free variables during substitution
def lift (l : Nat) : Tm → Tm
  | .unit => .unit
  | .pi σ τ  => .pi (lift l σ) (lift (l + 1) τ)
  | .sum σ τ => .sum (lift l σ) (lift (l + 1) τ)
  | .iden σ s t => .iden (lift l σ) (lift l s) (lift l t)
  | .univ => .univ
  | .var i =>
      if i < l
        then .var i
        else .var (i + 1)
  | .tt => .tt
  | .lam s t => .lam (lift l s) (lift (l + 1) t)
  | .app s t => .app (lift l s) (lift l t)
  | .pair s t => .pair (lift l s) (lift (l + 1) t)
  | .prj₁ s => .prj₁ (lift l s)
  | .prj₂ s => .prj₂ (lift l s)
  | .refl σ t => .refl (lift l σ) (lift l t)

def substitute (s : Tm) (t : Tm) (j : Nat) : Tm :=
  match s with
  | .unit => .unit
  | .pi σ τ  => .pi (substitute σ t j) (substitute τ (lift 0 t) (j + 1))
  | .sum σ τ => .sum (substitute σ t j) (substitute τ (lift 0 t) (j + 1))
  | .iden σ m n => .iden σ (substitute m t j) (substitute n t j)
  | .univ => .univ
  | .var i =>
      if i < j
        then .var i
        else if i = j
          then t
          else .var (i - 1)
  | .tt => .tt
  | .lam m n => .lam (substitute m t j) (substitute n (lift 0 t) (j + 1))
  | .app m n => .app (substitute m t j) (substitute n t j)
  | .pair m n => .pair (substitute m t j) (substitute n (lift 0 t) (j + 1))
  | .prj₁ m => .prj₁ (substitute m t j)
  | .prj₂ m => .prj₂ (substitute m t j)
  | .refl σ m => .refl (substitute σ t j) (substitute m t j)
