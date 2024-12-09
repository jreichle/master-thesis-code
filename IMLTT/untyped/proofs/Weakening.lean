import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

theorem weakening_var_lift {ρ ρ' : Weak m n} :
    (∀x, weaken_var x ρ = weaken_var x ρ')
    → (∀x, weaken_var x (.lift ρ) = weaken_var x (.lift ρ')) :=
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
    (∀x, weaken_var x ρ = weaken_var x ρ')
    → (∀j {x: Fin (n + j)}, weaken_var x (lift_weak_n j ρ) = weaken_var x (lift_weak_n j ρ')) :=
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
    (∀ i, weaken_var i ρ = weaken_var i ρ')
    → (∀ t, weaken t ρ = weaken t ρ') :=
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
    weaken_var x (.lift .id) = (weaken_var x .id) :=
  by
    match x with
    | .mk i h =>
      match i with
      | 0 => rfl
      | i' + 1 => rfl

theorem weakening_var_lift_n_id {n m : Nat} {x : Fin (n + m)} :
    weaken_var x (lift_weak_n m .id) = (weaken_var x .id) :=
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
    ∀ {x: Fin n}, weaken_var x .id = x :=
  by
    simp [weaken_var]

theorem weakening_id :
    ∀{t : Tm n}, weaken t .id = t :=
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
    weaken t (.lift .id) = t :=
  by
    have h :=  weakening_id (t := t)
    rw (config := {occs := .pos [2]}) [←h]
    apply weakening_var_weaken
    intro i
    apply weakening_var_lift_id

theorem weakening_var_comp {ρ : Weak l m} {ρ' : Weak m n} {x : Fin n} :
    weaken_var (weaken_var x ρ') ρ = weaken_var x (comp_weaken ρ ρ') :=
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
    weaken (weaken t ρ') ρ = weaken t (comp_weaken ρ ρ') :=
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
    | .indSigma A B C c p =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply And.intro
          · apply weakening_comp
          · apply And.intro
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
    comp_weaken (.shift .id) ρ = comp_weaken (.lift ρ) (.shift .id) :=
  by
    match ρ with
    | .id =>
      rfl
    | .shift ρ' =>
      apply congrArg Weak.shift (weakening_lift_shift_comp (ρ := ρ'))
    | .lift ρ' =>
      rfl

theorem weakening_shift_id {ρ : Weak m n} {t : Tm n} :
    weaken (weaken t ρ) (.shift .id) = weaken t (.shift ρ) :=
  by
    apply weakening_comp

theorem weakening_shift_id_lift {ρ : Weak m n} {t : Tm n} :
    weaken (weaken t (.shift .id)) (.lift ρ) = weaken t (.shift ρ) :=
  by
    rw [weakening_comp]
    rw [←weakening_lift_shift_comp]
    rfl

theorem weakening_shift_id_outside {ρ : Weak m n} {t : Tm n} :
    weaken (weaken t ρ) (.shift .id) = weaken (weaken t (.shift .id)) (.lift ρ) :=
  by
    rw [weakening_shift_id_lift]
    rw [weakening_comp]
    simp [comp_weaken]

-- other (lemmatas needed in some proof)

#reduce ((Tm.pi : Tm 1 → Tm 2 → Tm 1) v(0) v(1))⌊.shift .id⌋
#reduce ((Tm.pi : Tm 1 → Tm 2 → Tm 1) v(0) v(1))⌊.shift (.shift .id)⌋
#reduce ((Tm.pi : Tm 1 → Tm 2 → Tm 1) v(0) v(1))⌊(.shift .id)⌋⌊.shift .id⌋
#reduce ((Tm.refl : Tm 1 → Tm 1 → Tm 1) v(0) v(1))⌊.shift .id⌋
#reduce ((Tm.refl : Tm 1 → Tm 1 → Tm 1) v(0) v(1))⌊.shift (.shift .id)⌋
#reduce ((Tm.refl : Tm 1 → Tm 1 → Tm 1) v(0) v(1))⌊.shift .id⌋⌊.shift .id⌋

-- FIXME: lemma is wrong! see .var case

-- theorem weakening_lift_shift {S : Tm (n + 1)} {ρ : Weak m n} :
--     S⌊.lift (.shift ρ)⌋ = S⌊.lift ρ⌋⌊.lift (.shift .id)⌋ :=
--   by
--     match S with
--     | .unit => 
--       simp [weaken]
--     | .empty => 
--       simp [weaken]
--     | .pi A B => 
--       simp [weaken]
--       apply And.intro
--       · apply weakening_lift_shift
--       · simp [lift_weak_n]
--         rw [weakening_comp]
--         apply weakening_var_weaken
--         simp [weaken_var]
--         intro i
--         rfl
--     | .sigma A B =>
--       simp [weaken]
--       apply And.intro
--       · apply weakening_lift_shift
--       · simp [lift_weak_n]
--         rw [weakening_comp]
--         apply weakening_var_weaken
--         simp [weaken_var]
--         intro i
--         rfl
--     | .iden A a a' =>
--       simp [weaken]
--       apply And.intro
--       · apply weakening_lift_shift
--       · apply And.intro
--         · apply weakening_lift_shift
--         · apply weakening_lift_shift
--     | .univ =>
--       simp [weaken]
--     | .var i =>
--       simp [weaken]
--       simp [weaken_var]
--       match i with
--       | .mk i' hFin =>
--         match i' with
--         | .zero => rfl
--         | .succ j =>
--           simp []
--           sorry
--       -- match i with
--       -- | ⟨0, _⟩ => sorry
--       -- | ⟨x' + 1, h⟩ => sorry
--     | .tt =>
--       simp [weaken]
--     | .indUnit A b a =>
--       simp [weaken]
--       simp [lift_weak_n]
--       sorry
--     | .indEmpty A b =>
--       simp [weaken]
--       simp [lift_weak_n]
--       sorry
--     | .lam A b =>
--       simp [weaken]
--       simp [lift_weak_n]
--       sorry
--     | .app f a => sorry
--     | .pairSigma a b => sorry
--     | .indSigma A B C c p =>
--       simp [weaken]
--       simp [lift_weak_n]
--       sorry
--     | .refl A a => sorry
--     | .j A B b a a' p =>
--       simp [weaken]
--       simp [lift_weak_n]
--       sorry

theorem weakening_shift_double {S : Tm n} {ρ : Weak m n} : 
    S⌊.shift (.shift ρ)⌋ = S⌊.shift ρ⌋⌊.shift .id⌋ :=
  by
    rw [←weakening_shift_id]

theorem weakening_comp_shift {S : Tm n} {ρ : Weak m n} :
    S⌊.shift .id ∘ ρ⌋ = S⌊ρ⌋⌊.shift .id⌋ :=
  by
    simp [comp_weaken]
    apply (Eq.symm weakening_shift_id)
