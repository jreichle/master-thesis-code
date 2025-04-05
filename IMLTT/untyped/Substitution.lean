import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening

import Aesop

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
  | .nat => .nat
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
  | .zeroNat => .zeroNat
  | .succNat x => .succNat (substitute σ x)
  | .indNat A z s n => .indNat (substitute (lift_subst_n 1 σ) A) (substitute σ z)
                        (substitute (lift_subst_n 2 σ) s) (substitute σ n)
  | .refl A a => .refl (substitute σ A) (substitute σ a)
  | .j A B b a a' p => .j (substitute σ A) (substitute (lift_subst_n 3 σ) B)
                        (substitute (lift_subst_n 1 σ) b) (substitute σ a) (substitute σ a')
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

-- helpers:
def substitute_head (σ : Subst m (n + 1)) : Tm m :=
  substitute σ v(0)

def weaken_tail (ρ : Weak m (n + 1)) : Weak m n :=
  match ρ with
  | .id =>
    sorry
  | .shift ρ' =>
    sorry
  | .lift σ' =>
    sorry

def substitute_tail (σ : Subst m (n + 1)) : Subst m n :=
  match σ with
  | .weak ρ =>
    sorry
    -- .weak (weaken_tail ρ)
  | .shift σ' =>
    .shift (substitute_tail σ')
  | .lift σ' =>
    .shift σ'
  | .extend σ' t =>
    σ'

def substitute_zero (a : Tm n) (t : Tm (n + 1)) : Tm n :=
  substitute (.extend (.weak .id) a) t

--- FIXME: change everything to only use this
def zero_substitution (a : Tm n) : Subst n (n + 1) :=
  .extend (.weak .id) a

theorem substitute_n_helper {l n : Nat} :
    l ≤ n → ¬(l < n) → l = n :=
  by
    intro h1 h2
    rw [Nat.not_lt] at h2
    apply Iff.mpr Nat.eq_iff_le_and_ge
    apply And.intro
    · apply h1
    · apply h2

def n_substitution {l n : Nat} (leq : l ≤ n) (a : Tm l) : Subst n (n + 1) :=
  match n with
  | .zero =>
    have heq : l = Nat.zero := Iff.mp Nat.le_zero leq
    .extend (.weak .id) (heq ▸ a)
  | .succ n' =>
    if h : l < n' + 1 then
      .lift (n_substitution (Nat.le_of_lt_succ h) a)
    else
      have heq : l = Nat.succ n' := substitute_n_helper leq h
      .extend (.weak .id) (heq ▸ a)

def n_substitution_shift {l n : Nat} (leq : l ≤ n) (a : Tm l) : Subst n n :=
  match n with
  | .zero =>
    .weak .id
  | .succ n' =>
    if h : l < n' + 1 then
      .lift (n_substitution_shift (Nat.le_of_lt_succ h) a)
    else
      have heq : l = Nat.succ n' := substitute_n_helper leq h
      .extend (.weak (.shift .id)) (heq ▸ a)

prefix:96 "ₛ" => Subst.weak
prefix:97 "↑ₛ" => Subst.shift
prefix:97 "⇑ₛ" => Subst.lift
infixl:97 "ₙ⇑ₛ" => lift_subst_n
infixl:96 ", " => Subst.extend -- FIXME: change , (interferences with pattern matching)
infixl:96 "ₚ∘ₛ" => comp_weaken_substitute
infixl:96 "ₛ∘ₚ" => comp_substitute_weaken
infixl:96 "ₛ∘ₛ" => comp_substitute_substitute
notation:95 A "⌈" σ "⌉" => substitute σ A
notation:95 A "⌈" σ "⌉ᵥ" => substitute_var σ A
notation:95 A "⌈" σ "⌉₀" => substitute_zero σ A
notation:95 a "/₀" => zero_substitution a
notation:95 a "/ₙ" le => n_substitution le a
notation:95 a "↑/ₙ" le => n_substitution_shift le a
