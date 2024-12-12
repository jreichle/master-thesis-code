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

def weaken_var (ρ : Weak m n) (x : Fin n) : Fin m :=
  match ρ with
  | .id => x
  | .shift ρ => .succ (weaken_var ρ x)
  | .lift ρ =>
    match x with
    | ⟨0, _⟩ => 0
    | ⟨x' + 1, h⟩ => .succ (weaken_var ρ (Fin.mk x' (Nat.lt_of_succ_lt_succ h)))

def weaken (ρ : Weak m n) (t : Tm n) : Tm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (weaken ρ A) (weaken (lift_weak_n 1 ρ) B)
  | .sigma A B => .sigma (weaken ρ A) (weaken (lift_weak_n 1 ρ) B)
  | .iden A a a' => .iden (weaken ρ A) (weaken ρ a) (weaken ρ a')
  | .univ => .univ
  | .var i => weaken_var ρ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (weaken (lift_weak_n 1 ρ) A) (weaken ρ b) (weaken ρ a)
  | .indEmpty A b => .indEmpty (weaken (lift_weak_n 1 ρ) A) (weaken ρ b)
  | .lam A b => .lam (weaken ρ A) (weaken (lift_weak_n 1 ρ) b)
  | .app f a => .app (weaken ρ f) (weaken ρ a)
  | .pairSigma a b => .pairSigma (weaken ρ a) (weaken ρ b)
  | .indSigma A B C c p => .indSigma (weaken ρ A) (weaken (lift_weak_n 1 ρ) B)
                            (weaken (lift_weak_n 1 ρ) C) (weaken (lift_weak_n 2 ρ) c) (weaken ρ p)
  | .refl A a => .refl (weaken ρ A) (weaken ρ a)
  | .j A B b a a' p => .j (weaken ρ A) (weaken (lift_weak_n 3 ρ) B) (weaken ρ b)
                        (weaken ρ a) (weaken ρ a') (weaken ρ p)

def shift_tm : Tm n → Tm (n + 1)
  | t => weaken (.shift .id) t

notation:max "idₚ" => Weak.id
prefix:97 "↑ₚ" => Weak.shift -- TODO: change 'associativity' to prevent having to use parenthesis?
prefix:97 "⇑ₚ" => Weak.lift
infixl:96 "∘" => comp_weaken
notation:95 A "⌊" ρ "⌋" => weaken ρ A
