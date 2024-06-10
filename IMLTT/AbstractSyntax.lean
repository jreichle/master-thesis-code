inductive Tm where
  -- types
  | unit : Tm
  | pi   : Tm → Tm → Tm
  | sum  : Tm → Tm → Tm
  | iden : Tm → Tm → Tm → Tm
  | univ : Tm
  -- terms
  | var  : Nat → Tm -- !!!de Bruijn!!!
  | tt   : Tm
  | lam  : Tm → Tm → Tm
  | app  : Tm → Tm → Tm
  | pair : Tm → Tm → Tm
  | prj₁ : Tm → Tm
  | prj₂ : Tm → Tm
  | refl : Tm → Tm → Tm

abbrev Ctx := List Tm
notation "(" Γ "; " A ")" => A :: Γ
notation "(" Γ "; " Δ ")" => Δ ++ Γ

-- types
notation "⊤" => Tm.unit
notation "Π" σ ", " τ => Tm.pi σ τ
notation "Σ" σ ", " τ => Tm.sum σ τ
notation "Id " σ " (" x ", " y")" => Tm.iden σ x y -- might not want to use mixfix
-- terms
notation "()" => Tm.tt
notation "λ " T ", " t => Tm.lam T t
notation "⟨" T ", " t "⟩" => Tm.pair T t
notation "refl " σ " (" t ")" => Tm.refl σ t

instance : Coe Nat Tm where
  coe := .var
instance : OfNat Tm n where
  ofNat := n
