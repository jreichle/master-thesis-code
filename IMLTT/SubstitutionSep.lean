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

-- apply weakening to term


def lift_weak_n (i : Nat) (ρ : Weak) : Weak :=
  match i with
  | 0 => ρ
  | i' + 1 => .lift (lift_weak_n i' ρ)

def weaken_var (i : Nat) : Weak → Nat
  | .id => i
  | .shift ρ => (weaken_var i ρ) + 1
  | .lift ρ =>
    match i with
    | 0 => 0
    | i' + 1 => (weaken_var i' ρ) + 1

def weaken (t : Tm) (ρ : Weak) : Tm :=
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
  | .pairSigma a b => .pairSigma (weaken a ρ) (weaken b (lift_weak_n 1 ρ))
  | .indSigma A B C c p => .indSigma (weaken A ρ) (weaken B (lift_weak_n 1 ρ)) (weaken C (lift_weak_n 1 ρ))
                            (weaken c (lift_weak_n 2 ρ)) (weaken p ρ)
  | .refl A a => .refl (weaken A ρ) (weaken a ρ)
  | .j A B b a a' p => .j (weaken A ρ) (weaken B (lift_weak_n 3 ρ)) (weaken b (lift_weak_n 1 ρ))
                        (weaken a ρ) (weaken a' ρ) (weaken p ρ)

def shift_tm : Tm → Tm
  | t => weaken t (.shift .id)

-- apply weakening to substitution (Nat → Tm):

def id_subst : Nat → Tm :=
  .var

def shift_subst (σ : Nat → Tm) : Nat → Tm
  | i => shift_tm (σ i)

def lift_subst (σ : Nat → Tm) : Nat → Tm
  | 0 => 0
  | i + 1 => shift_subst σ i

def extend_subst (σ : Nat → Tm) (t : Tm) : Nat → Tm
  | 0 => t
  | (i + 1) => σ i

mutual
  def comp_subst (σ σ' : Nat → Tm) : Nat → Tm
    | i => sub (σ' i) σ

  def parse_weak (ρ : Weak) : Nat → Tm :=
    match ρ with
    | .id => id_subst
    | .shift ρ => shift_subst (parse_weak ρ)
    | .lift ρ => lift_subst (parse_weak ρ)

  def parse_subst (σ : Subst) : Nat → Tm :=
    match σ with
    | .weak ρ => parse_weak ρ
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

def substitute_zero (t : Tm) (a : Tm) : Tm :=
  substitute t (.extend (.weak .id) a)

def substitute_list (ts : List Tm) : Subst :=
  match ts with
  | [] => .weak .id
  | t :: ts' => .extend (substitute_list ts') t

def parse_weak_comp (ρ : Weak) (σ : Subst) : Nat → Tm
  | i => weaken ((parse_subst σ) i) ρ

def subst_weak_comp (σ : Subst) (ρ : Weak) : Nat → Tm
  | i => (parse_subst σ) (weaken_var i ρ)


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
