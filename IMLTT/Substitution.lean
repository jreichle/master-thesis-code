import IMLTT.AbstractSyntax

-- lift term to avoid capturing free variables during substitution
def lift (l : Nat) : Tm → Tm
  | .unit => .unit
  | .pi A B  => .pi (lift l A) (lift (l + 1) B)
  | .sum A B => .sum (lift l A) (lift (l + 1) B)
  | .iden A s t => .iden (lift l A) (lift l s) (lift l t)
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
  | .refl A t => .refl (lift l A) (lift l t)

def substitute (s : Tm) (t : Tm) (j : Nat) : Tm :=
  match s with
  | .unit => .unit
  | .pi A B  => .pi (substitute A t j) (substitute B (lift 0 t) (j + 1))
  | .sum A B => .sum (substitute A t j) (substitute B (lift 0 t) (j + 1))
  | .iden A m n => .iden A (substitute m t j) (substitute n t j)
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
  | .refl A m => .refl (substitute A t j) (substitute m t j)

def substitute_ctx (Γ : Ctx) (t : Tm) (j : Nat) : Ctx :=
  match Γ with
  | .empty => .empty
  | .extend Γ' A => (substitute_ctx Γ' t j) ⬝ (substitute A t j)
