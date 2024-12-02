import IMLTT.untyped.AbstractSyntax

inductive Weak : Nat → Nat → Type where
  | id : Weak n n
  | shift : Weak m n → Weak (m + 1) n
  | lift : Weak m n → Weak (m + 1) (n + 1)

def comp_weaken (ρ : Weak l m) (ρ' : Weak m n) : Weak l n :=
  match ρ with
  | .id => ρ'
  | .shift γ => .shift (comp_weaken γ ρ')
  | .lift γ  =>
    match ρ' with
    | .id => .lift γ
    | .shift γ' => .shift (comp_weaken γ γ')
    | .lift γ' => .lift (comp_weaken γ γ')

def shift_weak_n (i : Nat) (ρ : Weak m n) : Weak (m + i) n :=
  match i with
  | 0 => ρ
  | i' + 1 => .shift (shift_weak_n i' ρ)

def lift_weak_n (i : Nat) (ρ : Weak m n) : Weak (m + i) (n + i) :=
  match i with
  | 0 => ρ
  | i' + 1 => .lift (lift_weak_n i' ρ)

def weaken_var (x : Fin n) (ρ : Weak m n) : Fin m :=
  match ρ with
  | .id => x
  | .shift ρ => .succ (weaken_var x ρ)
  | .lift ρ =>
    match x with
    | ⟨0, _⟩ => 0
    | ⟨x' + 1, h⟩ => .succ (weaken_var (Fin.mk x' (Nat.lt_of_succ_lt_succ h)) ρ)

def weaken (t : Tm n) (ρ : Weak m n) : Tm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (weaken A ρ) (weaken B (lift_weak_n 1 ρ))
  | .sigma A B => .sigma (weaken A ρ) (weaken B (lift_weak_n 1 ρ))
  | .iden A a a' => .iden (weaken A ρ) (weaken a ρ) (weaken a' ρ)
  | .univ => .univ
  | .var i => weaken_var i ρ
  | .tt => .tt
  | .indUnit A b a => .indUnit (weaken A (lift_weak_n 1 ρ)) (weaken b ρ) (weaken a ρ)
  | .indEmpty A b => .indEmpty (weaken A (lift_weak_n 1 ρ)) (weaken b ρ)
  | .lam A b => .lam (weaken A ρ) (weaken b (lift_weak_n 1 ρ))
  | .app f a => .app (weaken f ρ) (weaken a ρ)
  | .pairSigma a b => .pairSigma (weaken a ρ) (weaken b ρ)
  | .indSigma A B C c p => .indSigma (weaken A ρ) (weaken B (lift_weak_n 1 ρ)) 
                            (weaken C (lift_weak_n 1 ρ)) (weaken c (lift_weak_n 2 ρ)) (weaken p ρ)
  | .refl A a => .refl (weaken A ρ) (weaken a ρ)
  | .j A B b a a' p => .j (weaken A ρ) (weaken B (lift_weak_n 3 ρ)) (weaken b ρ)
                        (weaken a ρ) (weaken a' ρ) (weaken p ρ)

def shift_tm : Tm n → Tm (n + 1)
  | t => weaken t (.shift .id)

notation : max "id" => Weak.id
prefix : 90 "↑" => Weak.shift -- TODO: change 'associativity' to prevent having to use parenthesis?
prefix : 90 "⇑" => Weak.lift
infixl:70 "∘" => comp_weaken
notation:60 A "⌊" ρ "⌋" => weaken A ρ
