import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening

inductive Subst : Nat → Nat → Type where
  | weak : Weak m n → Subst m n
  | shift : Subst m n → Subst (m + 1) n
  | lift : Subst m n → Subst (m + 1) (n + 1)
  | extend : Subst m n → Tm m → Subst m (n + 1)

def substitute_var (σ : Subst m n) (x : Fin n) : Tm m :=
  match σ with
  | .weak ρ => weaken ρ x
  | .shift σ' => shift_tm (substitute_var σ' x)
  | .lift σ' =>
    match x with
    | ⟨0, _⟩ => .var (.mk 0 (by simp []))
    | ⟨x' + 1, h⟩ => shift_tm (substitute_var σ' (.mk x' (by simp [Nat.lt_of_succ_lt_succ h])))
  | .extend σ' t =>
    match x with
    | ⟨0, _⟩ => t
    | ⟨x' + 1, h⟩ => substitute_var σ' (.mk x' (Nat.lt_of_succ_lt_succ h))

def lift_subst_n (i : Nat) (σ : Subst m n) : Subst (m + i) (n + i) :=
  match i with
  | 0 => σ
  | i' + 1 => .lift (lift_subst_n i' σ)

def substitute (σ : Subst m n) (t : Tm n) : Tm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (substitute σ A) (substitute (lift_subst_n 1 σ) B)
  | .sigma A B => .sigma (substitute σ A) (substitute (lift_subst_n 1 σ) B)
  | .iden A a a' => .iden (substitute σ A) (substitute σ a) (substitute σ a')
  | .univ => .univ
  | .var i => substitute_var σ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (substitute (lift_subst_n 1 σ) A) (substitute σ b) (substitute σ a)
  | .indEmpty A b => .indEmpty (substitute (lift_subst_n 1 σ) A) (substitute σ b)
  | .lam A b => .lam (substitute σ A) (substitute (lift_subst_n 1 σ) b)
  | .app f a => .app (substitute σ f) (substitute σ a)
  | .pairSigma a b => .pairSigma (substitute σ a) (substitute σ b)
  | .indSigma A B C c p => .indSigma (substitute σ A) (substitute (lift_subst_n 1 σ) B)
                            (substitute (lift_subst_n 1 σ) C) (substitute (lift_subst_n 2 σ) c)
                            (substitute σ p)
  | .refl A a => .refl (substitute σ A) (substitute σ a)
  | .j A B b a a' p => .j (substitute σ A) (substitute (lift_subst_n 3 σ) B)
                        (substitute σ b) (substitute σ a) (substitute σ a')
                        (substitute σ p)

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
    | .extend σ' t => .shift (.extend (comp_weaken_substitute ρ' σ') (weaken ρ' t))
  | .lift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken (.lift ρ') ξ)
    | .shift σ' => .shift (comp_weaken_substitute ρ' σ')
    | .lift σ' => .lift (comp_weaken_substitute ρ' σ')
    | .extend σ' t => .extend (comp_weaken_substitute (.lift ρ') σ') (weaken (.lift ρ') t)

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
  | .extend ξ' t => .extend (comp_substitute_substitute σ ξ') (substitute σ t)

-- def comp (t : Tm n) (σ : Subst l m) (σ' : Subst m n) : Tm l :=
--   substitute (comp_substitute_substitute σ σ') t

def comp_subst (t : Tm n) (σ : Subst l m) (σ' : Subst m n) : Tm l :=
  substitute σ (substitute σ' t)

def weak_subst (t : Tm n) (ρ : Weak l m) (σ : Subst m n) : Tm l :=
  weaken ρ (substitute σ t)

def subst_weak (t : Tm n) (σ : Subst l m) (ρ : Weak m n) : Tm l :=
  substitute σ (weaken ρ t)

-- helpers:

def substitute_zero (a : Tm n) (t : Tm (n + 1)) : Tm n :=
  substitute (.extend (.weak .id) a) t

prefix:96 "ₛ" => Subst.weak
prefix:97 "↑ₛ" => Subst.shift
prefix:97 "⇑ₛ" => Subst.lift
infixl:97 "ₙ⇑ₛ" => lift_subst_n
infixl:96 ", " => Subst.extend
infixl:96 "∘ₛ" => comp_subst
infixl:96 "ₚ∘ₛ" => comp_weaken_substitute
infixl:96 "ₛ∘ₚ" => comp_substitute_weaken
infixl:96 "ₛ∘ₛ" => comp_substitute_substitute
notation:95 A "⌈" σ "⌉" => substitute σ A
notation:95 A "⌈" σ "⌉ᵥ" => substitute_var σ A
notation:95 A "⌈" σ "⌉₁" => substitute_zero σ A
