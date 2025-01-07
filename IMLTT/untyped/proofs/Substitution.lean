import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import Aesop

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
