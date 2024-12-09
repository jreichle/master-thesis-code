import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening

inductive Subst : Nat → Nat → Type where
  | weak : Weak m n → Subst m n
  | shift : Subst m n → Subst (m + 1) n
  | lift : Subst m n → Subst (m + 1) (n + 1)
  | extend : Subst m n → Tm m → Subst m (n + 1)

def substitute_var (x : Fin n) (σ : Subst m n) : Tm m :=
  match σ with
  | .weak ρ => weaken x ρ
  | .shift σ' => shift_tm (substitute_var x σ')
  | .lift σ' =>
    match x with
    | ⟨0, _⟩ => .var (.mk 0 (by simp []))
    | ⟨x' + 1, h⟩ => shift_tm (substitute_var (.mk x' (by simp [Nat.lt_of_succ_lt_succ h])) σ')
  | .extend σ' t =>
    match x with
    | ⟨0, _⟩ => t
    | ⟨x' + 1, h⟩ => substitute_var (.mk x' (Nat.lt_of_succ_lt_succ h)) σ'

def lift_subst_n (i : Nat) (σ : Subst m n) : Subst (m + i) (n + i) :=
  match i with
  | 0 => σ
  | i' + 1 => .lift (lift_subst_n i' σ)

def substitute (t : Tm n) (σ : Subst m n) : Tm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (substitute A σ) (substitute B (lift_subst_n 1 σ))
  | .sigma A B => .sigma (substitute A σ) (substitute B (lift_subst_n 1 σ))
  | .iden A a a' => .iden (substitute A σ) (substitute a σ) (substitute a' σ)
  | .univ => .univ
  | .var i => substitute_var i σ
  | .tt => .tt
  | .indUnit A b a => .indUnit (substitute A (lift_subst_n 1 σ)) (substitute b σ) (substitute a σ)
  | .indEmpty A b => .indEmpty (substitute A (lift_subst_n 1 σ)) (substitute b σ)
  | .lam A b => .lam (substitute A σ) (substitute b (lift_subst_n 1 σ))
  | .app f a => .app (substitute f σ) (substitute a σ)
  | .pairSigma a b => .pairSigma (substitute a σ) (substitute b σ)
  | .indSigma A B C c p => .indSigma (substitute A σ) (substitute B (lift_subst_n 1 σ)) 
                            (substitute C (lift_subst_n 1 σ)) (substitute c (lift_subst_n 2 σ))
                            (substitute p σ)
  | .refl A a => .refl (substitute A σ) (substitute a σ)
  | .j A B b a a' p => .j (substitute A σ) (substitute B (lift_subst_n 3 σ))
                        (substitute b σ) (substitute a σ) (substitute a' σ)
                        (substitute p σ)

def comp_substitute_weaken (σ : Subst l m) (ρ : Weak m n) : Subst l n :=
  match ρ with
  | .id => σ
  | .shift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken ξ (.shift ρ'))
    | .shift σ' => .shift (comp_substitute_weaken σ' (.shift ρ'))
    | .lift σ' => .shift (comp_substitute_weaken σ' ρ')
    | .extend σ' t => comp_substitute_weaken σ' ρ'
  | .lift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken ξ (.lift ρ'))
    | .shift σ' => .shift (comp_substitute_weaken σ' (.lift ρ'))
    | .lift σ' => .lift (comp_substitute_weaken σ' ρ')
    | .extend σ' t => .extend (comp_substitute_weaken σ' ρ') t

def comp_weaken_substitute (ρ : Weak l m) (σ : Subst m n) : Subst l n :=
  match ρ with
  | .id => σ
  | .shift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken (.shift ρ') ξ)
    | .shift σ' => .shift (comp_weaken_substitute ρ' (.shift σ'))
    | .lift σ' => .shift (comp_weaken_substitute ρ' (.lift σ'))
    | .extend σ' t => .shift (.extend (comp_weaken_substitute ρ' σ') (weaken t ρ'))
  | .lift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken (.lift ρ') ξ)
    | .shift σ' => .shift (comp_weaken_substitute ρ' σ')
    | .lift σ' => .lift (comp_weaken_substitute ρ' σ')
    | .extend σ' t => .extend (comp_weaken_substitute (.lift ρ') σ') (weaken t (.lift ρ'))

def comp_substitute_substitute (σ : Subst l m) (σ' : Subst m n) : Subst l n :=
  match σ' with
  | .weak ρ' => comp_substitute_weaken σ ρ'
  | .shift ξ' =>
    match σ with
    | .weak ρ => comp_weaken_substitute ρ (.shift ξ')
    | .shift ξ => .shift (comp_substitute_substitute ξ (.shift ξ'))
    | .lift ξ => .shift (comp_substitute_substitute ξ ξ')
    | .extend ξ t => comp_substitute_substitute ξ ξ'
  | .lift ξ' =>
    match σ with
    | .weak ρ => comp_weaken_substitute ρ (.lift ξ')
    | .shift ξ => .shift (comp_substitute_substitute ξ (.lift ξ'))
    | .lift ξ => .lift (comp_substitute_substitute ξ ξ')
    | .extend ξ t => .extend (comp_substitute_substitute ξ ξ') t
  | .extend ξ' t => .extend (comp_substitute_substitute σ ξ') (substitute t σ)

-- FIXME: congr to above?
def comp_subst (t : Tm n) (σ : Subst l m) (σ' : Subst m n) : Tm l :=
  substitute (substitute t σ') σ

def weak_subst (t : Tm n) (ρ : Weak l m) (σ : Subst m n) : Tm l :=
  weaken (substitute t σ) ρ

def subst_weak (t : Tm n) (σ : Subst l m) (ρ : Weak m n) : Tm l :=
  substitute (weaken t ρ) σ

-- helpers:

def substitute_zero (t : Tm (n + 1)) (a : Tm n) : Tm n :=
  substitute t (.extend (.weak .id) a)

prefix : 80 "ₛ" => Subst.weak
prefix:90 "↑ₛ" => Subst.shift
prefix:90 "⇑ₛ" => Subst.lift
infixl:70 "∘ₛ" => comp_subst -- problems from here
infixl:70 ", " => Subst.extend
notation:60 A "⌈" σ "⌉" => substitute A σ
