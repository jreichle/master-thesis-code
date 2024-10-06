import IMLTT.AbstractSyntax

inductive Subst where -- TODO: (id, a, id, a) not possible?
  | id : Subst
  | shift : Subst → Subst
  | lift : Subst → Subst
  | subst : (Nat → Tm) → Subst
  | comp : Subst → Subst → Subst -- FIXME: comp destroys termination -- delete and then add function for comp?

def depth_weak : Subst → Nat
  | .id => 1
  | .shift σ => 1 + (depth_weak σ)
  | .lift σ => 1 + (depth_weak σ)
  | .subst _ => 1
  | .comp σ σ' => max (depth_weak σ) (depth_weak σ')

def extend_subst (sub : Nat → Tm) (t : Tm) : Nat → Tm
  | 0 => t
  | (i + 1) => sub i

mutual
  def substitute_var (i : Nat) : Subst → Tm
    | .id => .var i
    | .shift σ =>
      match σ with
      | .id => .var (i + 1)
      | σ' => substitute (substitute_var i σ') (.shift .id)
    | .lift σ =>
      match i with
      | 0 => .var 0
      | i' + 1 => substitute (substitute_var i' σ) (.shift .id)
    | .subst σ => σ i
    | .comp σ σ' => substitute (substitute_var i σ') σ -- FIXME: better comp
    termination_by depth_tm

  def substitute (t : Tm) (σ : Subst) : Tm :=
    match t with
    | .unit => .unit
    | .empty => .empty
    | .pi A B => .pi (substitute A σ) (substitute B (.lift σ))
    | .sigma A B => .sigma (substitute A σ) (substitute B (.lift σ))
    | .iden A a a' => .iden (substitute A σ) (substitute a σ) (substitute a' σ)
    | .univ => .univ
    | .var i => substitute_var i σ
    | .tt => .tt
    | .indUnit A b a => .indUnit (substitute A (.lift σ)) (substitute b σ) (substitute a σ)
    | .indEmpty A b => .indEmpty (substitute A (.lift σ)) (substitute b σ)
    | .lam A b => .lam (substitute A σ) (substitute b (.lift σ))
    | .app f a => .app (substitute f σ) (substitute a σ)
    | .pairSigma a b => .pairSigma (substitute a σ) (substitute b (.lift σ))
    | .indSigma A B C c p => .indSigma (substitute A σ) (substitute B (.lift σ)) 
                              (substitute C (.lift σ)) (substitute C (.lift (.lift σ)))
                              (substitute p σ) -- FIXME: Σ-comp is wrong - last assumption
    | .refl A a => .refl (substitute A σ) (substitute a σ)
    | .j A B b a a' p => .j (substitute A σ) (substitute B (.lift (.lift (.lift σ))))
                          (substitute b (.lift σ)) (substitute a σ) (substitute a' σ)
                          (substitute p σ) -- FIXME: j-rule is wrong
      termination_by depth_tm
end

notation "id" => Subst.id
notation "↑" σ => Subst.shift σ
notation "⇑" σ => Subst.lift σ
notation "∘" => Subst.comp
notation A "[" σ "]" => substitute A σ

