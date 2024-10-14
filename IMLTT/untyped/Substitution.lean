import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening

-- TODO: extract Tm recursor and give it a function to deal with binders
-- TODO: is it possibe to readd comp?

inductive Subst : Nat → Nat → Type where -- TODO: n → Tm m here?
  | weak : Weak m n  → Subst m n
  | shift : Subst m n → Subst (m + 1) n
  | lift : Subst m n → Subst (m + 1) (n + 1)
  | extend : Subst m n → Tm m → Subst m (n + 1)

def substVar (x : Fin n) (σ : Subst m n) : Tm m :=
  match σ with
  | .weak ρ => weaken x ρ
  | .shift σ' => shift_tm (substVar x σ')
  | .lift σ' =>
    match x with
    | ⟨0, h⟩ => .var (Fin.mk 0 (by simp []))
    | ⟨x' + 1, h⟩ => shift_tm (substVar (Fin.mk x' (by simp [Nat.lt_of_succ_lt_succ h])) σ')
  | .extend σ' t =>
    match x with
    | ⟨0, h⟩ => .var (Fin.mk 0 (sorry)) -- FIXME: does this even work?
    | ⟨x' + 1, h⟩ => substVar (Fin.mk x' (Nat.lt_of_succ_lt_succ h)) σ'

mutual
  def lift_subst_n (σ : Subst m n) (i : Nat) : Subst (m + i) (n + i) :=
    match i with
    | 0 => σ
    | i' + 1 => .lift (lift_subst_n σ i')

  def substitute (t : Tm n) (σ : Subst m n) : Tm m :=
    match t with
    | .unit => .unit
    | .empty => .empty
    | .pi A B => .pi (substitute A σ) (substitute B (lift_subst_n σ 1))
    | .sigma A B => .sigma (substitute A σ) (substitute B (lift_subst_n σ 1))
    | .iden A a a' => .iden (substitute A σ) (substitute a σ) (substitute a' σ)
    | .univ => .univ
    | .var i => substVar i σ
    | .tt => .tt
    | .indUnit A b a => .indUnit (substitute A (lift_subst_n σ 1)) (substitute b σ) (substitute a σ)
    | .indEmpty A b => .indEmpty (substitute A (lift_subst_n σ 1)) (substitute b σ)
    | .lam A b => .lam (substitute A σ) (substitute b (lift_subst_n σ 1))
    | .app f a => .app (substitute f σ) (substitute a σ)
    | .pairSigma a b => .pairSigma (substitute a σ) (substitute b σ)
    | .indSigma A B C c p => .indSigma (substitute A σ) (substitute B (lift_subst_n σ 1)) 
                              (substitute C (lift_subst_n σ 1)) (substitute c (lift_subst_n σ 2))
                              (substitute p σ)
    | .refl A a => .refl (substitute A σ) (substitute a σ)
    | .j A B b a a' p => .j (substitute A σ) (substitute B (lift_subst_n σ 3))
                          (substitute b (lift_subst_n σ 1)) (substitute a σ) (substitute a' σ)
                          (substitute p σ)
end

def subst_subst (t : Tm n) (σ : Subst l m) (σ' : Subst m n) : Tm l :=
  substitute (substitute t σ') σ

def weak_subst (t : Tm n) (ρ : Weak l m) (σ : Subst m n) : Tm l :=
  weaken (substitute t σ) ρ

def subst_weak (t : Tm n) (σ : Subst l m) (ρ : Weak m n) : Tm l :=
  substitute (weaken t ρ) σ

-- helpers:

def substitute_zero (t : Tm (n + 1)) (a : Tm n) : Tm n :=
  substitute t (.extend (.weak .id) a)

notation "id" => Weak.id
notation "↑" => Weak.shift
notation "⇑" => Weak.lift
notation "⇑_" i => lift_weak_n i
notation ρ "∘" ρ' => comp_weaken ρ ρ'
notation A "[" ρ "]" => weaken A ρ

notation "↑" => Subst.shift
notation "⇑" => Subst.lift
infixl:66 "∘" => Subst.comp
infixl:66 ", " => Subst.extend
notation A "[" σ "]" => substitute A σ
