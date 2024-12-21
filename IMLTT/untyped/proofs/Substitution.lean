import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

theorem substitution_var_lift {σ σ' : Subst m n} :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (x : Fin (n + 1)), v(x)⌈⇑ₛσ⌉ = v(x)⌈⇑ₛσ'⌉ :=
  by
    intro h x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        rfl
      | succ i' =>
        apply congrArg shift_tm (h (.mk i' (Nat.lt_of_succ_lt_succ hFin)))


theorem substitution_var_lift_n {σ σ' : Subst m n} :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (x : Fin (n + l)), v(x)⌈l ₙ⇑ₛσ⌉ = v(x)⌈l ₙ⇑ₛσ'⌉ :=
  by
    intro h x
    cases l with
    | zero =>
      simp [lift_subst_n]
      apply h
    | succ i' =>
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          rfl
        | succ i' =>
          simp [lift_subst_n]
          apply substitution_var_lift
          apply substitution_var_lift_n
          apply h

theorem substitution_var_substitute {σ σ' : Subst m n} :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (t : Tm n), t⌈σ⌉ = t⌈σ'⌉ :=
  by
    intro h t
    match t with
    | .unit =>
      simp [substitute]
    | .empty =>
      simp [substitute]
    | .pi A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift_n h
    | .sigma A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift_n h
    | .iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply And.intro
        · apply substitution_var_substitute h
        · apply substitution_var_substitute h
    | .univ =>
      simp [substitute]
    | .var x =>
      apply h
    | .tt =>
      simp [substitute]
    | .indUnit A b a =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute
        apply substitution_var_lift h
      · apply And.intro
        · apply substitution_var_substitute h
        · apply substitution_var_substitute h
    | .indEmpty A b =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute
        apply substitution_var_lift h
      · apply substitution_var_substitute h
    | .lam A b => 
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift h
    | .app f a => 
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute h
    | .pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute h
    | .indSigma A B C c p =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply And.intro
        · apply substitution_var_substitute
          apply substitution_var_lift h
        · apply And.intro
          · apply substitution_var_substitute
            apply substitution_var_lift h
          · apply And.intro
            · apply substitution_var_substitute
              apply substitution_var_lift_n h
            · apply substitution_var_substitute h
    | .refl A a =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute h
    | .j A B b a a' p => 
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply And.intro
        · apply substitution_var_substitute
          apply substitution_var_lift_n h
        · apply And.intro
          · apply substitution_var_substitute h
          · apply And.intro
            · apply substitution_var_substitute h
            · apply And.intro
              · apply substitution_var_substitute h
              · apply substitution_var_substitute h

theorem substitution_var_lift_id {x : Fin (n + 1)} :
    v(x)⌈⇑ₛ(ₛidₚ)⌉ = v(x)⌈ₛidₚ⌉ :=
  by
    match x with
    | .mk i h =>
      match i with
      | 0 => rfl
      | i' + 1 => rfl

theorem substitution_var_lift_n_id {n m : Nat} {x : Fin (n + m)} :
    v(x)⌈m ₙ⇑ₛ(ₛidₚ)⌉ = v(x)⌈ₛidₚ⌉ :=
  by
    match m with
    | 0 => rfl
    | m' + 1 =>
      match x with
      | .mk i h =>
        match i with
        | 0 => rfl
        | i' + 1 =>
          have h := substitution_var_lift_n_id (n := n) (x := .mk i' (Nat.lt_of_succ_lt_succ h)) 
          apply congrArg shift_tm h

theorem substitution_id {t : Tm n} :
    t⌈ₛidₚ⌉ = t :=
  by
    match t with
    | .unit =>
      simp [substitute]
    | .empty =>
      simp [substitute]
    | .pi A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · have h := substitution_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
    | .sigma A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · have h := substitution_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
    | .iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply And.intro
        · apply substitution_id
        · apply substitution_id
    | .univ =>
      simp [substitute]
    | .var x =>
      simp [substitute]
      rfl
    | .tt =>
      simp [substitute]
    | .indUnit A b a =>
      simp [substitute]
      apply And.intro
      · have h := substitution_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
      · apply And.intro
        · apply substitution_id
        · apply substitution_id
    | .indEmpty A b =>
      simp [substitute]
      apply And.intro
      · have h := substitution_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
      · apply substitution_id
    | .lam A b =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · have h := substitution_id (t := b)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
    | .app f a =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply substitution_id
    | .pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply substitution_id
    | .indSigma A B C c p =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply And.intro
        · have h := substitution_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply substitution_var_substitute
          intro x
          apply substitution_var_lift_n_id
        · apply And.intro
          · have h := substitution_id (t := C)
            rw (config := {occs := .pos [2]}) [←h]
            apply substitution_var_substitute
            intro x
            apply substitution_var_lift_n_id
          · apply And.intro
            · have h := substitution_id (t := c)
              rw (config := {occs := .pos [2]}) [←h]
              apply substitution_var_substitute
              intro x
              apply substitution_var_lift_n_id
            · apply substitution_id
    | .refl A a =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply substitution_id
    | .j A B b a a' p =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply And.intro
        · have h := substitution_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply substitution_var_substitute
          intro x
          apply substitution_var_lift_n_id
        · apply And.intro
          · apply substitution_id
          · apply And.intro
            · apply substitution_id
            · apply And.intro
              · apply substitution_id
              · apply substitution_id


theorem substitution_weakening {ρ : Weak m n} {x : Fin n} :
    v(x)⌈ₛρ⌉ = v(x)⌊ρ⌋ :=
  by
    simp [weaken]
    simp [substitute]
    rfl

theorem substitution_conv_lift_id :
    ∀ (x : Fin (n + 1)), v(x)⌈ₛ⇑ₚidₚ⌉ = v(x)⌈⇑ₛ(ₛidₚ)⌉ :=
  by
    intro x
    simp [substitute]
    cases x with
    | mk i h =>
      cases i with
      | zero =>
        rfl
      | succ i' =>
        rfl

theorem substitution_lift_id {t : Tm (n + 1)} :
    t⌈ₛ⇑ₚidₚ⌉ = t :=
  by
    have h := substitution_id (t := t)
    rw (config := {occs := .pos [2]}) [←h]
    apply substitution_var_substitute
    intro i
    rw [←substitution_var_lift_id]
    apply substitution_conv_lift_id

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

theorem substitution_shift_id {σ : Subst m n} {x : Fin n} :
    v(x)⌈σ⌉⌊↑ₚidₚ⌋ = v(x)⌈↑ₛσ⌉ :=
  by
    simp [substitute]
    simp [substitute_var]
    rfl

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
        rw [←weakening_shift_id]
        rw [ih]
        rw [substitution_shift_id]
      | lift σ' =>
        simp [comp_weaken_substitute]
        rw [←weakening_shift_id]
        rw [ih]
        rw [substitution_shift_id]
      | extend σ' s =>
        rw [←weakening_shift_id]
        rw [ih]
        rw [substitution_shift_id]
        simp [substitute]
        simp [substitute_var]
        cases x with
        | mk i hFin =>
          cases i with
          | zero => 
            simp [substitute_var]
            simp [shift_tm]
            simp [comp_weaken_substitute]
            sorry
          | succ i' =>
            simp [comp_weaken_substitute]
            simp [substitute_var]
            sorry
    | lift ρ' ih =>
      cases σ with
      | weak γ => 
       simp [comp_weaken_substitute]
       simp [substitution_weakening]
       simp [weakening_comp]
      | shift σ' =>
        simp [comp_weaken_substitute]
        sorry
      | lift σ' =>
        sorry
      | extend σ' s =>
        sorry


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
      sorry
      -- simp [substitution_var_comp]
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
    | .indSigma A B C c p =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply And.intro
        · simp [lift_weak_n]
          simp [lift_subst_n]
          rw [←substitution_lift_comp_ρσ]
          apply substitution_comp_ρσ
        · apply And.intro
          · simp [lift_weak_n]
            simp [lift_subst_n]
            rw [←substitution_lift_comp_ρσ]
            apply substitution_comp_ρσ
          · apply And.intro
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


theorem substitution_comp_subst_weaken {t : Tm n} :
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
      · apply substitution_comp_subst_weaken
      · simp [lift_weak_n]
        simp [lift_subst_n]
        sorry
    | .sigma A B => sorry
    | .iden A a a' =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · apply And.intro
        · apply substitution_comp_subst_weaken
        · apply substitution_comp_subst_weaken
    | .univ =>
      rfl
    | .var x =>
      sorry
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · sorry
      · apply And.intro
        · apply substitution_comp_subst_weaken
        · apply substitution_comp_subst_weaken
    | .indEmpty A b =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · sorry
      · apply substitution_comp_subst_weaken
    | .lam A b =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · simp [lift_weak_n]
        simp [lift_subst_n]
        sorry
    | .app f a =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · apply substitution_comp_subst_weaken
    | .pairSigma a b =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · apply substitution_comp_subst_weaken
    | .indSigma A B C c p =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · apply And.intro
        · sorry
        · apply And.intro
          · sorry
          · apply And.intro
            · sorry
            · apply substitution_comp_subst_weaken
    | .refl A a =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · apply substitution_comp_subst_weaken
    | .j A B b a a' p =>
      simp [weaken]
      simp [substitute]
      apply And.intro
      · apply substitution_comp_subst_weaken
      · apply And.intro
        · sorry
        · apply And.intro
          · apply substitution_comp_subst_weaken
          · apply And.intro
            · apply substitution_comp_subst_weaken
            · apply And.intro
              · apply substitution_comp_subst_weaken
              · apply substitution_comp_subst_weaken
