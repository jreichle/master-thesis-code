import IMLTT.AbstractSyntax

-- ASTs

-- TODO: is it possibe to readd comp?
inductive Weak where
  | id : Weak
  | shift : Weak → Weak
  | lift : Weak → Weak

inductive Subst where
  | weak : Weak → Subst
  | shift : Subst → Subst
  | lift : Subst → Subst
  | extend : Subst → Tm → Subst

-- AST → AST

def comp_weaken (ρ ρ' : Weak) : Weak :=
  match ρ with
  | .id => ρ'
  | .shift γ => .shift (comp_weaken γ ρ')
  | .lift γ  =>
    match ρ' with
    | .id => .lift γ
    | .shift γ' => .shift (comp_weaken γ γ')
    | .lift γ' => .lift (comp_weaken γ γ')

def subst_from_list (ts : List Tm) : Subst :=
  match ts with
  | [] => .weak .id
  | t :: ts' => .extend (subst_from_list ts') t

-- weakening: Nat → Nat

def id_weak : Nat → Nat :=
  id

def shift_weak (ρ : Nat → Nat) : Nat → Nat :=
  fun i ↦ ρ i + 1

def lift_weak (ρ : Nat → Nat) : Nat → Nat :=
  fun i ↦
    match i with 
    | 0 => 0
    | i' + 1 => (ρ i') + 1

def parse_weak (ρ : Weak) : Nat → Nat :=
  match ρ with
  | .id => id_weak
  | .shift ρ => shift_weak (parse_weak ρ)
  | .lift ρ => lift_weak (parse_weak ρ)

def lift_weak_n (j : Nat) (ρ : Nat → Nat) : Nat → Nat
  | i =>
    match j with
    | 0 => ρ i
    | j' + 1 => (lift_weak_n j' ρ) i

def weak (t : Tm) (ρ : Nat → Nat) : Tm :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (weak A ρ) (weak B (lift_weak_n 1 ρ))
  | .sigma A B => .sigma (weak A ρ) (weak B (lift_weak_n 1 ρ))
  | .iden A a a' => .iden (weak A ρ) (weak a ρ) (weak a' ρ)
  | .univ => .univ
  | .var i => ρ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (weak A (lift_weak_n 1 ρ)) (weak b ρ) (weak a ρ)
  | .indEmpty A b => .indEmpty (weak A (lift_weak_n 1 ρ)) (weak b ρ)
  | .lam A b => .lam (weak A ρ) (weak b (lift_weak_n 1 ρ))
  | .app f a => .app (weak f ρ) (weak a ρ)
  | .pairSigma a b => .pairSigma (weak a ρ) (weak b (lift_weak_n 1 ρ))
  | .indSigma A B C c p => .indSigma (weak A ρ) (weak B (lift_weak_n 1 ρ)) (weak C (lift_weak_n 1 ρ))
                            (weak c (lift_weak_n 2 ρ)) (weak p ρ)
  | .refl A a => .refl (weak A ρ) (weak a ρ)
  | .j A B b a a' p => .j (weak A ρ) (weak B (lift_weak_n 3 ρ)) (weak b (lift_weak_n 1 ρ))
                        (weak a ρ) (weak a' ρ) (weak p ρ)

def weaken (t : Tm) (ρ : Weak) : Tm :=
  weak t (parse_weak ρ)

def comp_weak (ρ ρ' : Nat → Nat) : Nat → Nat
  | i => ρ (ρ' i)

-- helpers

def weak_var (i : Nat) (ρ : Weak) : Nat :=
  (parse_weak ρ) i

def shift_tm : Tm → Tm
  | t => weaken t (.shift .id)

def parse_weak_to_sub (ρ : Nat → Nat) : Nat → Tm
  | i => .var (ρ i)

def id_subst : Nat → Tm :=
  .var

-- substitution: Nat → Tm

def shift_tm_f : Tm → Tm
  | t => weak t (parse_weak (.shift .id))

def shift_subst (σ : Nat → Tm) : Nat → Tm
  | i => shift_tm_f (σ i)

def lift_subst (σ : Nat → Tm) : Nat → Tm
  | 0 => 0
  | i + 1 => shift_subst σ i

def extend_subst (σ : Nat → Tm) (t : Tm) : Nat → Tm
  | 0 => t
  | (i + 1) => σ i

mutual
  def comp_subst (σ σ' : Nat → Tm) : Nat → Tm
    | i => sub (σ' i) σ

  def parse_subst (σ : Subst) : Nat → Tm :=
    match σ with
    | .weak ρ => parse_weak_to_sub (parse_weak ρ)
    | .shift σ => shift_subst (parse_subst σ)
    | .lift σ => lift_subst (parse_subst σ)
    | .extend σ t => extend_subst (parse_subst σ) t

  def sub (t : Tm) (σ : Nat → Tm) : Tm :=
    match t with
    | .unit => .unit
    | .empty => .empty
    | .pi A B => .pi (sub A σ) (sub B (lift_subst σ))
    | .sigma A B => .sigma (sub A σ) (sub B (lift_subst σ))
    | .iden A a a' => .iden (sub A σ) (sub a σ) (sub a' σ)
    | .univ => .univ
    | .var i => σ i
    | .tt => .tt
    | .indUnit A b a => .indUnit (sub A (lift_subst σ)) (sub b σ) (sub a σ)
    | .indEmpty A b => .indEmpty (sub A (lift_subst σ)) (sub b σ)
    | .lam A b => .lam (sub A σ) (sub b (lift_subst σ))
    | .app f a => .app (sub f σ) (sub a σ)
    | .pairSigma a b => .pairSigma (sub a σ) (sub b (lift_subst σ))
    | .indSigma A B C c p => .indSigma (sub A σ) (sub B (lift_subst σ)) 
                              (sub C (lift_subst σ)) (sub c (lift_subst (lift_subst σ)))
                              (sub p σ) -- FIXME: Σ-comp is wrong - last assumption
    | .refl A a => .refl (sub A σ) (sub a σ)
    | .j A B b a a' p => .j (sub A σ) (sub B (lift_subst (lift_subst (lift_subst σ))))
                          (sub b (lift_subst σ)) (sub a σ) (sub a' σ)
                          (sub p σ) -- FIXME: j-rule is wrong
end

def substitute (t : Tm) (σ : Subst) : Tm :=
  sub t (parse_subst σ)

def parse_weak_comp (ρ : Weak) (σ : Subst) : Nat → Tm
  | i => weaken ((parse_subst σ) i) ρ

def subst_weak_comp (σ : Subst) (ρ : Weak) : Nat → Tm
  | i => (parse_subst σ) (weak_var i ρ)

-- helpers:
def substitute_zero (t : Tm) (a : Tm) : Tm :=
  substitute t (.extend (.weak .id) a)

notation "id" => Weak.id
notation "↑" => Weak.shift
notation "⇑" => Weak.lift
notation "⇑_" i => lift_weak_n i
notation ρ "∘" ρ' => comp_weaken ρ ρ'
notation A "[" ρ "]" => weaken A ρ

notation "↑" => Subst.shift
notation "⇑" => Subst.lift
notation σ "∘" σ' => Subst.comp σ σ'
notation A "[" σ "]" => substitute A σ
