import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Conversion

-- comp_weaken

theorem weakening_var_comp {ρ : Weak l m} {ρ' : Weak m n} {x : Fin n} :
    x⌊ρ'⌋ᵥ⌊ρ⌋ᵥ = x⌊ρ ₚ∘ₚρ'⌋ᵥ :=
  by
    induction ρ with
    | id =>
      simp [weaken_var]
      rfl
    | shift γ ih =>
      rw [comp_weaken]
      simp [weaken_var]
      rw [←ih]
    | lift γ ih =>
      cases ρ' with
      | id =>
        simp [weaken_var]
      | shift γ' =>
        rw [comp_weaken]
        simp [weaken_var]
        rw [←ih]
        rfl
      | lift γ' =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero => rfl
          | succ i' =>
            rw [comp_weaken]
            simp [weaken_var]
            rw [←weakening_var_comp]
            rfl

theorem weakening_comp {ρ : Weak l m} {ρ' : Weak m n} {t : Tm n} :
    t⌊ρ'⌋⌊ρ⌋ = t⌊ρ ₚ∘ₚρ'⌋ :=
  by
    match t with
    | .unit =>
      rfl
    | .empty =>
      rfl
    | .pi A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .nat =>
      rfl
    | .iden A a a' => 
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply weakening_comp
    | .univ =>
      rfl
    | .var x =>
      simp [weaken]
      simp [←weakening_var_comp]
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply weakening_comp
    | .indEmpty A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .lam A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .app f a =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .pairSigma a b =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .firstSigma p =>
      simp [weaken]
      apply weakening_comp
    | .secondSigma p =>
      simp [weaken]
      apply weakening_comp
    | .zeroNat =>
      simp [weaken]
    | .succNat i =>
      simp [weaken]
      apply weakening_comp
    | .indNat A z s i =>
      simp [weaken]
      repeat' apply And.intro
      · apply weakening_comp
      · apply weakening_comp
      · apply weakening_comp
      · apply weakening_comp
    | .refl A a =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .j A B b a a' p =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply And.intro
          · apply weakening_comp
          · apply And.intro
            · apply weakening_comp
            · apply And.intro
              · apply weakening_comp
              · apply weakening_comp

theorem weakening_lift_shift_comp {ρ : Weak m n} :
    ↑ₚidₚ ₚ∘ₚ ρ = ⇑ₚρ ₚ∘ₚ ↑ₚidₚ :=
  by
    match ρ with
    | .id =>
      rfl
    | .shift ρ' =>
      apply congrArg Weak.shift (weakening_lift_shift_comp (ρ := ρ'))
    | .lift ρ' =>
      rfl

theorem weakening_shift_id {ρ : Weak m n} {t : Tm n} :
    t⌊ρ⌋⌊↑ₚidₚ⌋ = t⌊↑ₚρ⌋ :=
  by
    apply weakening_comp

theorem weakening_shift_id_lift {ρ : Weak m n} {t : Tm n} :
    t⌊↑ₚidₚ⌋⌊⇑ₚρ⌋ = t⌊↑ₚρ⌋ :=
  by
    rw [weakening_comp]
    rw [←weakening_lift_shift_comp]
    rfl

theorem weakening_shift_id_outside {ρ : Weak m n} {t : Tm n} :
    t⌊ρ⌋⌊↑ₚidₚ⌋ = t⌊↑ₚidₚ⌋⌊⇑ₚρ⌋ :=
  by
    rw [weakening_shift_id_lift]
    rw [weakening_comp]
    simp [comp_weaken]

theorem weakening_shift_double {S : Tm n} {ρ : Weak m n} : 
    S⌊↑ₚ↑ₚρ⌋ = S⌊↑ₚρ⌋⌊↑ₚidₚ⌋ :=
  by
    rw [←weakening_shift_id]

theorem weakening_comp_shift {S : Tm n} {ρ : Weak m n} :
    S⌊↑ₚidₚ ₚ∘ₚ ρ⌋ = S⌊ρ⌋⌊↑ₚidₚ⌋ :=
  by
    simp [comp_weaken]
    apply (Eq.symm weakening_shift_id)

-- comp_weaken_substitute

theorem substitution_lift_comp_ρσ {t : Tm (n + 1)} :
    t⌈⇑ₚρ ₚ∘ₛ⇑ₛσ⌉ = t⌈⇑ₛ(ρ ₚ∘ₛσ)⌉ :=
  by
    simp [comp_weaken_substitute]

theorem substitution_var_lift_n_comp_ρσ {n : Nat} {x : Fin (z + n + 1)} :
    v(x)⌈⇑ₚ n ₙ⇑ₚρ ₚ∘ₛ⇑ₛ n ₙ⇑ₛσ⌉ = v(x)⌈⇑ₛ n ₙ⇑ₛ(ρ ₚ∘ₛσ)⌉ :=
  by
    match n with
    | .zero =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero => 
          simp [comp_weaken_substitute]
          rfl
        | .succ i' =>
          simp [substitute]
          simp [comp_weaken_substitute]
          simp [lift_weak_n]
          simp [lift_subst_n]
    | .succ n' =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero =>
          simp [comp_weaken_substitute]
          rfl
        | .succ i' =>
          simp [comp_weaken_substitute]
          apply substitution_var_lift
          simp [lift_weak_n]
          simp [lift_subst_n]
          apply substitution_var_lift_n_comp_ρσ

theorem substitution_lift_n_comp_ρσ (l : Nat) {t : Tm (n + l)} :
    t⌈l ₙ⇑ₚρ ₚ∘ₛl ₙ⇑ₛσ⌉ = t⌈l ₙ⇑ₛ(ρ ₚ∘ₛσ)⌉ :=
  by
    match l with
    | 0 => 
      simp [lift_subst_n]
      simp [lift_weak_n]
    | l' + 1 =>
      simp [lift_subst_n]
      simp [lift_weak_n]
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp_ρσ

theorem substitution_var_shift_comp_ρσ {x : Fin n} :
    x⌈↑ₛ(ρ ₚ∘ₛσ)⌉ᵥ = x⌈(↑ₚρ ₚ∘ₛσ)⌉ᵥ :=
  by
    induction ρ generalizing x with
    | id =>
      cases σ with
      | weak ξ =>
        simp [comp_weaken_substitute]
        simp [comp_weaken]
        rfl
      | shift σ' =>
        simp [comp_weaken_substitute]
      | lift σ' =>
        simp [comp_weaken_substitute]
      | extend σ' s =>
        simp [comp_weaken_substitute]
        simp [weakening_id]
    | shift ρ' ih =>
      cases σ with
      | weak ξ =>
        simp [comp_weaken_substitute]
        simp [comp_weaken]
        rfl
      | shift σ' =>
        simp [←substitution_var_conv_shift_id]
        simp [←ih]
        simp [comp_weaken_substitute]
        simp [←substitution_var_conv_shift_id]
      | lift σ' =>
        simp [comp_weaken_substitute]
      | extend σ' s =>
        simp [←substitution_var_conv_shift_id]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            rw [comp_weaken_substitute]
            simp [substitute_var]
            simp [shift_tm]
            rw [comp_weaken_substitute]
            rw [←substitution_var_conv_shift_id]
            simp [substitute_var]
            simp [weakening_shift_id]
            rw [←weakening_shift_id]
            rfl
          | succ i' =>
            simp [comp_weaken_substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [substitution_var_conv_shift_id]
            simp [←substitution_var_conv_shift_id]
            rw [←substitution_var_shift_comp_ρσ]
            simp [←substitution_var_conv_shift_id]
    | lift ρ' ih =>
      cases σ with
      | weak ξ =>
        simp [comp_weaken_substitute]
        simp [comp_weaken]
        rfl
      | shift σ' =>
        simp [comp_weaken_substitute]
      | lift σ' =>
        simp [comp_weaken_substitute]
      | extend σ' s =>
        simp [comp_weaken_substitute]

theorem test1 :
    x⌈↑ₚρ ₚ∘ₛ(σ, s)⌉ᵥ = x⌈↑ₚρ ₚ∘ₛσ, (s⌊↑ₚρ⌋)⌉ᵥ :=
  by
    simp [comp_weaken_substitute]
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [substitute_var]
        simp [shift_tm]
        simp [weakening_shift_id]
      | succ i' =>
        cases ρ with
        | id =>
          simp [comp_weaken_substitute]
          simp [weakening_id]
          simp [substitute_var]
          simp [shift_tm]
          simp [←substitution_var_shift_comp_ρσ]
          simp [comp_weaken_substitute]
          simp [←substitution_var_conv_shift_id]
        | shift ρ' =>
          simp [substitute_var]
          simp [shift_tm]
          rw (config := {occs := .pos [2]}) [←substitution_var_shift_comp_ρσ]
          simp [substitution_var_conv_shift_id]
        | lift ρ' =>
          simp [substitute_var]
          simp [shift_tm]
          simp [←substitution_var_shift_comp_ρσ]
          simp [←substitution_var_conv_shift_id]

theorem substitution_var_comp_shift_extend_ρσ {x : Fin (n + 1)}:
    x⌈↑ₛ(ρ ₚ∘ₛ(σ, s))⌉ᵥ = x⌈↑ₛ(ρ ₚ∘ₛσ, (s⌊ρ⌋))⌉ᵥ :=
  by
    induction ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [weakening_id]
    | shift ρ' ih =>
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          simp [comp_weaken_substitute]
          simp [substitute_var]
          rw [←weakening_shift_id]
          rfl
        | succ i' =>
          simp [←substitution_conv_shift_comp_ρσ]
          rw (config := {occs := .pos [2]}) [comp_weaken_substitute]
          simp [←substitution_var_conv_shift_id]
          simp [test1]
    | lift ρ' ih =>
      simp [comp_weaken_substitute]

theorem substitution_var_comp_ρσ {ρ : Weak l m} {σ : Subst m n} {x : Fin n} :
    v(x)⌈σ⌉⌊ρ⌋ = v(x)⌈ρ ₚ∘ₛσ⌉ :=
  by
    induction ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [weakening_id]
    | shift ρ' ih =>
      cases σ with
      | weak γ => 
      simp [comp_weaken_substitute]
      simp [substitution_weakening]
      simp [weakening_comp]
      | shift σ' =>
        simp [comp_weaken_substitute]
        simp [substitute]
        simp [substitute_var]
        simp [shift_tm]
        simp [weakening_comp]
        simp [comp_weaken]
        rw [←weakening_shift_id]
        simp [←substitution_conv_var]
        simp [←ih]
        simp [←weakening_comp]
        rfl
      | lift σ' =>
        simp [comp_weaken_substitute]
        rw [←weakening_shift_id]
        rw [ih]
        simp [substitute]
        rw [substitution_var_conv_shift_id]
      | extend σ' s =>
        rw [←weakening_shift_id]
        rw [ih]
        simp [substitute]
        rw [substitution_var_conv_shift_id]
        simp [substitute_var]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [substitute_var]
            simp [shift_tm]
            simp [substitution_var_conv_shift_id]
            simp [comp_weaken_substitute]
            simp [substitution_var_comp_shift_extend_ρσ]
          | succ i' =>
            simp [shift_tm]
            simp [substitution_var_conv_shift_id]
            simp [comp_weaken_substitute]
            simp [substitution_var_comp_shift_extend_ρσ]
    | lift ρ' ih =>
      cases σ with
      | weak γ => 
        simp [comp_weaken_substitute]
        simp [substitution_weakening]
        simp [weakening_comp]
      | shift σ' =>
        simp [comp_weaken_substitute]
        simp [substitute]
        simp [substitute_var]
        simp [shift_tm]
        simp [weakening_shift_id_lift]
        rw [←weakening_shift_id]
        simp [substitute] at ih
        simp [ih]
      | lift σ' =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [comp_weaken_substitute]
            simp [substitute]
            simp [substitute_var]
            simp [weaken]
            rfl
          | succ i' =>
            simp [comp_weaken_substitute]
            simp [substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [weakening_comp]
            simp [comp_weaken]
            rw [←weakening_shift_id]
            simp [←weakening_comp]
            simp [weakening_id]
            simp [←substitution_conv_var]
            simp [substitution_var_comp_ρσ]
      | extend σ' s =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [comp_weaken_substitute]
            simp [substitute]
            simp [substitute_var]
            rfl
          | succ i' =>
            simp [comp_weaken_substitute]
            simp [substitute]
            simp [substitute_var]
            simp [←substitution_conv_var]
            simp [substitution_var_comp_ρσ]

theorem substitution_comp_ρσ {t : Tm n} :
    t⌈σ⌉⌊ρ⌋ = t⌈ρ ₚ∘ₛσ⌉ :=
  by
    match t with
    | .unit =>
      rfl
    | .empty =>
      rfl
    | .pi A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
    | .sigma A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
    | .nat =>
      rfl
    | .iden A a a' =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply And.intro
        · apply substitution_comp_ρσ
        · apply substitution_comp_ρσ
    | .univ =>
      rfl
    | .var x =>
      simp [substitute]
      apply substitution_var_comp_ρσ (x := x)
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
      · apply And.intro
        · apply substitution_comp_ρσ
        · apply substitution_comp_ρσ
    | .indEmpty A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .lam A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
    | .app f a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .pairSigma a b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .firstSigma p =>
      simp [substitute]
      simp [weaken]
      apply substitution_comp_ρσ
    | .secondSigma p =>
      simp [substitute]
      simp [weaken]
      apply substitution_comp_ρσ
    | .zeroNat =>
      simp [substitute]
      simp [weaken]
    | .succNat i =>
      simp [substitute]
      simp [weaken]
      apply substitution_comp_ρσ
    | .indNat A z s i =>
      simp [substitute]
      simp [weaken]
      repeat' apply And.intro
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
      · rw [←substitution_lift_n_comp_ρσ]
        apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .refl A a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .j A B b a a' p =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply And.intro
        · rw [←substitution_lift_n_comp_ρσ]
          apply substitution_comp_ρσ
        · apply And.intro
          · apply substitution_comp_ρσ
          · apply And.intro
            · apply substitution_comp_ρσ
            · apply And.intro
              · apply substitution_comp_ρσ
              · apply substitution_comp_ρσ

theorem substitution_lift_comp_σρ {t : Tm (n + 1)} :
    t⌈⇑ₛσ ₛ∘ₚ⇑ₚρ⌉ = t⌈⇑ₛ(σ ₛ∘ₚρ)⌉ :=
  by
    rfl

theorem substitution_var_lift_n_comp_σρ {l : Nat} {x : Fin (n + l + 1)} :
    v(x)⌈⇑ₛ l ₙ⇑ₛσ ₛ∘ₚ ⇑ₚ l ₙ⇑ₚρ⌉ = v(x)⌈⇑ₛ l ₙ⇑ₛ(σ ₛ∘ₚρ)⌉ :=
  by
    match l with
    | .zero =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero => 
          rfl
        | .succ i' =>
          simp [comp_substitute_weaken]
          simp [lift_subst_n]
          simp [lift_weak_n]
    | .succ n' =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero =>
          rfl
        | .succ i' =>
          simp [comp_weaken_substitute]
          apply substitution_var_lift
          simp [lift_weak_n]
          simp [lift_subst_n]
          apply substitution_var_lift_n_comp_σρ

theorem substitution_lift_n_comp_σρ {l : Nat} {t : Tm (n + l)} :
    t⌈l ₙ⇑ₛσ ₛ∘ₚl ₙ⇑ₚρ⌉ = t⌈l ₙ⇑ₛ(σ ₛ∘ₚρ)⌉ :=
  by
    match l with
    | .zero => rfl
    | .succ l' =>
      simp [lift_subst_n]
      simp [lift_weak_n]
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp_σρ

theorem substitution_conv_shift_id :
    t⌈σ⌉⌊↑ₚidₚ⌋ = t⌈↑ₛσ⌉ :=
  by
    simp [substitution_comp_ρσ]
    apply substitution_var_substitute
    simp [←substitution_comp_ρσ]
    apply substitution_var_conv_shift_id

theorem substitution_var_shift_id_lift :
    v(x)⌊↑ₚidₚ⌋⌈⇑ₛσ⌉ = v(x)⌈σ⌉⌊↑ₚidₚ⌋ :=
  by
    simp [weaken]
    simp [weaken_var]
    simp [substitute]
    simp [substitute_var]
    simp [shift_tm]
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp [weaken]
      | succ i' =>
        simp [weaken]

theorem substitution_var_comp_σρ {x : Fin n} :
    v(x)⌊ρ⌋⌈σ⌉ = v(x)⌈σ ₛ∘ₚρ⌉ :=
  by
    induction σ with
    | weak ξ =>
      cases ρ with
      | id =>
        simp [comp_substitute_weaken]
        rfl
      | shift ρ' =>
        simp [comp_substitute_weaken]
        simp [substitution_weakening]
        simp [←weakening_comp]
        rfl
      | lift ρ' =>
        simp [comp_substitute_weaken]
        simp [substitution_weakening]
        simp [←weakening_comp]
        rfl
    | shift σ' ih =>
      cases ρ with
      | id =>
        simp [comp_substitute_weaken]
        rfl
      | shift ρ' =>
        simp [comp_substitute_weaken]
        simp [substitute]
        simp [←substitution_var_conv_shift_id]
        simp [←substitution_conv_var]
        simp [←ih]
        simp [←weakening_conv_var]
      | lift ρ' =>
        simp [comp_substitute_weaken]
        simp [substitute]
        simp [←substitution_var_conv_shift_id]
        simp [←substitution_conv_var]
        simp [←ih]
        simp [←weakening_conv_var]
    | lift σ' ih =>
      cases ρ with
      | id =>
        simp [comp_substitute_weaken]
        rfl
      | shift ρ' =>
        simp [comp_substitute_weaken]
        simp [substitute]
        simp [←substitution_var_conv_shift_id]
        simp [←substitution_conv_var]
        simp [←ih]
        simp [←weakening_conv_var]
        rw [←weakening_shift_id]
        rw [weaken]
        simp [substitution_var_shift_id_lift]
      | lift ρ' =>
        simp [comp_substitute_weaken]
        simp [substitute]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [weaken_var]
            simp [substitute_var]
            rfl
          | succ i' =>
            simp [weaken_var]
            simp [substitute_var]
            simp [shift_tm]
            simp [←substitution_conv_var]
            rw [←substitution_var_comp_σρ]
            rfl
    | extend σ' s ih =>
      cases ρ with
      | id =>
        simp [comp_substitute_weaken]
        rfl
      | shift ρ' =>
        simp [comp_substitute_weaken]
        simp [←ih]
        simp [weaken]
        simp [weaken_var]
        simp [substitute]
        simp [substitute_var]
        rfl
      | lift ρ' =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [comp_substitute_weaken]
            rfl
          | succ i' =>
            simp [comp_substitute_weaken]
            simp [weaken]
            simp [weaken_var]
            simp [substitute]
            simp [substitute_var]
            simp [←substitution_conv_var]
            simp [←substitution_var_comp_σρ]
            rfl

theorem substitution_comp_σρ {t : Tm n} :
    t⌊ρ⌋⌈σ⌉ = t⌈σ ₛ∘ₚρ⌉ :=
  by
    match t with
    | .unit =>
      rfl
    | .empty =>
      rfl
    | .pi A B =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
    | .sigma A B =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
    | .nat =>
      rfl
    | .iden A a a' =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · apply And.intro
        · apply substitution_comp_σρ
        · apply substitution_comp_σρ
    | .univ =>
      rfl
    | .var x =>
      apply substitution_var_comp_σρ
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
      · apply And.intro
        · apply substitution_comp_σρ
        · apply substitution_comp_σρ
    | .indEmpty A b =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .lam A b =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
    | .app f a =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .pairSigma a b =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .firstSigma p =>
      simp [weaken]
      simp [substitute]
      apply substitution_comp_σρ
    | .secondSigma p =>
      simp [weaken]
      simp [substitute]
      apply substitution_comp_σρ
    | .zeroNat =>
      simp [weaken]
      simp [substitute]
    | .succNat i =>
      simp [weaken]
      simp [substitute]
      apply substitution_comp_σρ
    | .indNat A z s i =>
      simp [weaken]
      simp [substitute]
      repeat' apply And.intro
      · simp [lift_weak_n]
        rw [←substitution_lift_n_comp_σρ]
        apply substitution_comp_σρ
      · apply substitution_comp_σρ
      · simp [lift_weak_n]
        rw [←substitution_lift_n_comp_σρ]
        apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .refl A a =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .j A B b a a' p =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_σρ
      · apply And.intro
        · simp [lift_weak_n]
          rw [←substitution_lift_n_comp_σρ]
          apply substitution_comp_σρ
        · apply And.intro
          · apply substitution_comp_σρ
          · apply And.intro
            · apply substitution_comp_σρ
            · apply And.intro
              · apply substitution_comp_σρ
              · apply substitution_comp_σρ

theorem substitution_shift_id_lift :
    t⌊↑ₚidₚ⌋⌈⇑ₛσ⌉ = t⌈σ⌉⌊↑ₚidₚ⌋ :=
  by
    rw [substitution_comp_σρ]
    simp [comp_substitute_weaken]
    simp [substitution_conv_shift_id]

theorem substitution_lift_comp :
    t⌈⇑ₛσ ₛ∘ₛ⇑ₛσ'⌉ = t⌈⇑ₛ(σ ₛ∘ₛσ')⌉ :=
  by
    simp [comp_substitute_substitute]

theorem substitution_var_lift_n_comp :
    v(x)⌈⇑ₛ n ₙ⇑ₛσ ₛ∘ₛ ⇑ₛ n ₙ⇑ₛσ'⌉ = v(x)⌈⇑ₛn ₙ⇑ₛ(σ ₛ∘ₛσ')⌉ :=
  by
    cases n with
    | zero => 
      simp [lift_subst_n]
      simp [substitution_lift_comp]
    | succ n' =>
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          simp [comp_substitute_substitute]
          rfl
        | succ i' =>
          simp [comp_substitute_substitute]
          apply substitution_var_lift
          simp [lift_subst_n]
          apply substitution_var_lift_n_comp

theorem substitution_lift_n_comp (l : Nat) {t : Tm (n + l)} :
    t⌈l ₙ⇑ₛσ ₛ∘ₛl ₙ⇑ₛσ'⌉ = t⌈l ₙ⇑ₛ(σ ₛ∘ₛ σ')⌉ :=
  by
    match l with
    | 0 =>
      simp [lift_subst_n]
    | l' + 1 =>
      simp [lift_subst_n]
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp

theorem substitution_var_comp {x : Fin n} :
    v(x)⌈σ'⌉⌈σ⌉ = v(x)⌈σ ₛ∘ₛσ'⌉ :=
  by
    induction σ' with
    | weak ρ' =>
      simp [comp_substitute_substitute]
      simp [←substitution_comp_σρ]
      rfl
    | shift ξ' ih =>
      cases σ with
      | weak ρ =>
        simp [comp_substitute_substitute]
        simp [←substitution_comp_ρσ]
        simp [conversion_sub_weak]
      | shift ξ =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [←substitution_conv_var]
        simp [←substitution_conv_shift_id]
        rw [←substitution_var_comp]
        simp [substitution_conv_shift_id]
      | lift ξ =>
        simp [comp_substitute_substitute]
        simp [substitute]
        simp [←substitution_var_conv_shift_id]
        simp [←substitution_conv_var]
        rw [←substitution_var_comp]
        rw [substitution_shift_id_lift]
      | extend ξ s =>
        simp [comp_substitute_substitute]
        rw [←ih]
        simp [substitute]
        simp [substitute_var]
        simp [shift_tm]
        simp [substitution_comp_σρ]
        simp [comp_substitute_weaken]
    | lift ξ' ih =>
      cases σ with
      | weak ρ =>
        simp [comp_substitute_substitute]
        simp [←substitution_comp_ρσ]
        simp [conversion_sub_weak]
      | shift ξ =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [comp_substitute_substitute]
            simp [←substitution_var_conv_shift_id]
            simp [←substitution_conv_var]
            rw [←substitution_var_comp]
            simp [substitute]
          | succ i' =>
            simp [substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [comp_substitute_substitute]
            simp [←substitution_var_conv_shift_id]
            simp [←substitution_conv_var]
            rw [←substitution_var_comp]
            simp [substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [substitution_var_conv_shift_id]
            simp [substitution_conv_shift_id]
      | lift ξ =>
        simp [comp_substitute_substitute]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [substitute]
            simp [substitute_var]
            rfl
          | succ i' =>
            simp [substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [←substitution_conv_var]
            rw [←substitution_var_comp]
            simp [substitution_shift_id_lift]
      | extend ξ s =>
        simp [comp_substitute_substitute]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [substitute]
            simp [substitute_var]
            rfl
          | succ i' =>
            simp [substitute]
            simp [substitute_var]
            simp [shift_tm]
            simp [substitution_comp_σρ]
            simp [comp_substitute_weaken]
            simp [←substitution_conv_var]
            rw [ih]
    | extend ξ' s' ih =>
      simp [comp_substitute_substitute]
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          rfl
        | succ i' =>
          simp [substitute]
          simp [substitute_var]
          simp [←substitution_conv_var]
          rw [←ih]

theorem substitution_comp :
    t⌈σ'⌉⌈σ⌉ = t⌈σ ₛ∘ₛ σ'⌉ :=
  by
    cases t with
    | unit =>
      simp [substitute]
    | empty =>
      simp [substitute]
    | pi A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · simp [lift_subst_n]
        rw [←substitution_lift_comp]
        apply substitution_comp
    | sigma A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · simp [lift_subst_n]
        rw [←substitution_lift_comp]
        apply substitution_comp
    | nat =>
      simp [substitute]
    | iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply And.intro
        · apply substitution_comp
        · apply substitution_comp
    | univ =>
      simp [substitute]
    | var x =>
      apply substitution_var_comp
    | tt =>
      simp [substitute]
    | indUnit A b a =>
      simp [substitute]
      apply And.intro
      · simp [lift_subst_n]
        rw [←substitution_lift_comp]
        apply substitution_comp
      · apply And.intro
        · apply substitution_comp
        · apply substitution_comp
    | indEmpty A b =>
      simp [substitute]
      apply And.intro
      · simp [lift_subst_n]
        rw [←substitution_lift_comp]
        apply substitution_comp
      · apply substitution_comp
    | lam A b =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · simp [lift_subst_n]
        rw [←substitution_lift_comp]
        apply substitution_comp
    | app f a =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply substitution_comp
    | pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply substitution_comp
    | firstSigma p =>
      simp [substitute]
      apply substitution_comp
    | secondSigma p =>
      simp [substitute]
      apply substitution_comp
    | zeroNat =>
      simp [substitute]
    | succNat i =>
      simp [substitute]
      apply substitution_comp
    | indNat A z s i =>
      simp [substitute]
      repeat' apply And.intro
      · rw [←substitution_lift_n_comp]
        apply substitution_comp
      · apply substitution_comp
      · rw [←substitution_lift_n_comp]
        apply substitution_comp
      · apply substitution_comp
    | refl A a =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply substitution_comp
    | j A B b a a' p =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply And.intro
        · rw [←substitution_lift_n_comp]
          apply substitution_comp
        · apply And.intro
          · apply substitution_comp
          · apply And.intro
            · apply substitution_comp
            · apply And.intro
              · apply substitution_comp
              · apply substitution_comp
