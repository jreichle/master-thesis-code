import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

theorem weakening_conv_var :
    v(x)⌊ρ⌋ = x⌊ρ⌋ᵥ :=
  by
    simp [weaken]

theorem weakening_var_lift {ρ ρ' : Weak m n} :
    (∀x, x⌊ρ⌋ᵥ = x⌊ρ'⌋ᵥ) → (∀x, x⌊⇑ₚρ⌋ᵥ = x⌊⇑ₚρ'⌋ᵥ) :=
  by
    intro h x
    cases x with
    | mk i _h =>
      match i with
      | 0 => rfl
      | i' + 1 =>
        simp [weaken_var]
        apply h

theorem weakening_var_lift_n {ρ ρ' : Weak m n}:
    (∀x, x⌊ρ⌋ᵥ = x⌊ρ'⌋ᵥ)
    → (∀j {x: Fin (n + j)}, x⌊j ₙ⇑ₚ ρ⌋ᵥ = x⌊j ₙ⇑ₚ ρ'⌋ᵥ) :=
  by
    intro h x n
    cases x with
    | zero =>
      simp [lift_weak_n]
      apply h
    | succ i =>
      rw [lift_weak_n]
      apply weakening_var_lift
      apply weakening_var_lift_n
      apply h

theorem weakening_var_weaken :
    (∀ x, x⌊ρ⌋ᵥ = x⌊ρ'⌋ᵥ) → (∀ t, t⌊ρ⌋ = t⌊ρ'⌋) :=
  by
    intro h t
    match t with
    | .unit =>
      simp [weaken]
    | .empty =>
      simp [weaken]
    | .pi A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n h
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n h
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply And.intro
        · apply weakening_var_weaken h
        · apply weakening_var_weaken h
    | .univ =>
      simp [weaken]
    | .var x =>
      simp [weaken]
      apply h
    | .tt =>
      simp [weaken]
    | .indUnit A b a =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken
        apply weakening_var_lift_n
        apply h
      · apply And.intro
        · apply weakening_var_weaken h
        · apply weakening_var_weaken h
    | .indEmpty A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken
        apply weakening_var_lift_n h
      · apply weakening_var_weaken h
    | .lam A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        apply weakening_var_lift_n h
    | .app f a =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken h
    | .pairSigma a b =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken h
    | .indSigma A B C c p =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply And.intro
        · apply weakening_var_weaken
          apply weakening_var_lift_n h
        · apply And.intro
          · apply weakening_var_weaken
            apply weakening_var_lift_n h
          · apply And.intro
            · apply weakening_var_weaken
              apply weakening_var_lift_n h
            · apply weakening_var_weaken h
    | .refl A a =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken h
    | .j A B b a a' p =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply And.intro
        · apply weakening_var_weaken
          apply weakening_var_lift_n h
        · apply And.intro
          · apply weakening_var_weaken h
          · apply And.intro
            · apply weakening_var_weaken h
            · apply And.intro
              · apply weakening_var_weaken h
              · apply weakening_var_weaken h

theorem weakening_var_lift_id {n : Nat} {x : Fin (n + 1)} :
    x⌊⇑ₚidₚ⌋ᵥ = x⌊idₚ⌋ᵥ :=
  by
    match x with
    | .mk i h =>
      match i with
      | 0 => rfl
      | i' + 1 => rfl

theorem weakening_var_lift_n_id {n m : Nat} {x : Fin (n + m)} :
    x⌊m ₙ⇑ₚidₚ⌋ᵥ = x⌊idₚ⌋ᵥ :=
  by
    match m with
    | 0 => rfl
    | m' + 1 =>
      match x with
      | .mk i h =>
        match i with
        | 0 => rfl
        | i' + 1 =>
          rw [lift_weak_n]
          simp [weaken_var]
          rw [weakening_var_lift_n_id]
          rfl

theorem weakening_var_id :
    ∀ {x: Fin n}, weaken_var .id x = x :=
  by
    simp [weaken_var]

theorem weakening_id :
    ∀ {t : Tm n}, t⌊idₚ⌋ = t :=
  by
    intro t
    match t with
    | .unit =>
      simp [weaken]
    | .empty =>
      simp [weaken]
    | .pi A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · have h := weakening_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n_id
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · have h := weakening_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n_id
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply And.intro
        · apply weakening_id
        · apply weakening_id
    | .univ =>
      simp [weaken]
    | .var x =>
      simp [weaken]
      rfl
    | .tt =>
      simp [weaken]
    | .indUnit A b a =>
      simp [weaken]
      apply And.intro
      · have h := weakening_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n_id
      · apply And.intro
        · apply weakening_id
        · apply weakening_id
    | .indEmpty A b =>
      simp [weaken]
      apply And.intro
      · have h := weakening_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n_id
      · apply weakening_id
    | .lam A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · have h := weakening_id (t := b)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n_id
    | .app f a =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply weakening_id
    | .pairSigma a b => 
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply weakening_id
    | .indSigma A B C c p =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply And.intro
        · have h := weakening_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply weakening_var_weaken
          intro i
          apply weakening_var_lift_n_id
        · apply And.intro
          · have h := weakening_id (t := C)
            rw (config := {occs := .pos [2]}) [←h]
            apply weakening_var_weaken
            intro i
            apply weakening_var_lift_n_id
          · apply And.intro
            · have h := weakening_id (t := c)
              rw (config := {occs := .pos [2]}) [←h]
              apply weakening_var_weaken
              intro i
              apply weakening_var_lift_n_id
            · apply weakening_id
    | .refl A a => 
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply weakening_id
    | .j A B b a a' p =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply And.intro
        · have h := weakening_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply weakening_var_weaken
          intro i
          apply weakening_var_lift_n_id
        · apply And.intro
          · apply weakening_id
          · apply And.intro
            · apply weakening_id
            · apply And.intro
              · apply weakening_id
              · apply weakening_id

theorem weakening_lift_id {t : Tm (n + 1)} : 
    t⌊⇑ₚidₚ⌋ = t :=
  by
    have h :=  weakening_id (t := t)
    rw (config := {occs := .pos [2]}) [←h]
    apply weakening_var_weaken
    intro i
    apply weakening_var_lift_id
