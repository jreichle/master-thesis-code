import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

theorem substitution_var_lift {σ σ' : Subst m n} :
    (∀x, substitute σ (.var x) = substitute σ' (.var x))
    → (∀x, substitute (.lift σ) (.var x) = substitute (.lift σ') (.var x)):=
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
    (∀x, substitute σ (.var x) = substitute σ' (.var x))
    → (∀x, substitute (lift_subst_n l σ) (.var x) = substitute (lift_subst_n l σ') (.var x)) :=
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
    (∀x, substitute σ (.var x) = substitute σ' (.var x))
    → (∀t, substitute σ t = substitute σ' t) :=
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
    substitute (.lift (.weak .id)) (.var x) = substitute (.weak .id) (.var x) :=
  by
    match x with
    | .mk i h =>
      match i with
      | 0 => rfl
      | i' + 1 => rfl

theorem substitution_var_lift_n_id {n m : Nat} {x : Fin (n + m)} :
    substitute (lift_subst_n m (.weak .id)) (.var x) = substitute (.weak .id) (.var x) :=
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
    substitute (.weak .id) t = t :=
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

theorem substitution_conv_lift_id :
    ∀x, substitute (.weak (.lift (.id : Weak n n))) (.var x) 
      = substitute (.lift (.weak .id)) (.var x) :=
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
    substitute (.weak (.lift .id)) t = t :=
  by
    have h := substitution_id (t := t)
    rw (config := {occs := .pos [2]}) [←h]
    apply substitution_var_substitute
    intro i
    rw [←substitution_var_lift_id]
    apply substitution_conv_lift_id

theorem substitution_lift_comp_ρσ {t : Tm (n + 1)} :
    (substitute (comp_weaken_substitute (.lift ρ) (.lift σ)) t)
    = substitute (.lift (comp_weaken_substitute ρ σ)) t :=
  by
    simp [comp_weaken_substitute]

theorem substitution_var_lift_n_comp_ρσ
    {n : Nat} {x : Fin (z + n + 1)} :
    substitute (comp_weaken_substitute (.lift (lift_weak_n n ρ)) (.lift (lift_subst_n n σ))) 
                (.var x)
    = substitute (.lift (lift_subst_n n (comp_weaken_substitute ρ σ))) (.var x) :=
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
    (substitute (comp_weaken_substitute (lift_weak_n l ρ) (lift_subst_n l σ)) t)
    = substitute (lift_subst_n l (comp_weaken_substitute ρ σ)) t :=
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

theorem substitution_lift_comp_σρ {t : Tm (n + 1)} :
    substitute (comp_substitute_weaken (.lift σ) (.lift ρ)) t
    = substitute (.lift (comp_substitute_weaken σ ρ)) t :=
  by
    rfl

theorem substitution_var_lift_n_comp_σρ {l : Nat} {x : Fin (n + l + 1)} :
    substitute (comp_substitute_weaken (.lift (lift_subst_n l σ)) (.lift (lift_weak_n l ρ))) (.var x)
    = substitute (.lift (lift_subst_n l (comp_substitute_weaken σ ρ))) (.var x) :=
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
    substitute (comp_substitute_weaken (lift_subst_n l σ) (lift_weak_n l ρ)) t
    = substitute (lift_subst_n l (comp_substitute_weaken σ ρ)) t :=
  by
    match l with
    | .zero => rfl
    | .succ l' =>
      simp [lift_subst_n]
      simp [lift_weak_n]
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp_σρ

#check substitution_var_lift
#check substitution_var_substitute


-- ⊢ B⌈⇑ₛσ⌉⌊⇑ₚρ⌋ = B⌈⇑ₚρ ₚ∘ₛ⇑ₛσ⌉
theorem test {σ σ' : Subst m n} {ρ ρ' : Weak l m} :
    (∀(x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (x : Fin (n + 1)), v(x)⌈⇑ₛσ⌉ = v(x)⌈⇑ₛσ'⌉ :=
  by
    sorry


theorem substitution_comp_weaken_subst {t : Tm n} :
    weaken ρ (substitute σ t)
    = substitute (comp_weaken_substitute ρ σ) t :=
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
      · apply substitution_comp_weaken_subst
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        sorry
    | .sigma A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · simp [lift_weak_n]
        simp [lift_subst_n]
        rw [←substitution_lift_comp_ρσ]
        sorry
    | .iden A a a' =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · apply And.intro
        · apply substitution_comp_weaken_subst
        · apply substitution_comp_weaken_subst
    | .univ =>
      rfl
    | .var x =>
      sorry
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · sorry
      · apply And.intro
        · apply substitution_comp_weaken_subst
        · apply substitution_comp_weaken_subst
    | .indEmpty A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · sorry
      · apply substitution_comp_weaken_subst
    | .lam A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · simp [lift_weak_n]
        simp [lift_subst_n]
        sorry
    | .app f a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · apply substitution_comp_weaken_subst
    | .pairSigma a b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · apply substitution_comp_weaken_subst
    | .indSigma A B C c p =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · apply And.intro
        · sorry
        · apply And.intro
          · sorry
          · apply And.intro
            · sorry
            · apply substitution_comp_weaken_subst
    | .refl A a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · apply substitution_comp_weaken_subst
    | .j A B b a a' p =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply substitution_comp_weaken_subst
      · apply And.intro
        · sorry
        · apply And.intro
          · apply substitution_comp_weaken_subst
          · apply And.intro
            · apply substitution_comp_weaken_subst
            · apply And.intro
              · apply substitution_comp_weaken_subst
              · apply substitution_comp_weaken_subst

theorem substitution_comp_subst_weaken {t : Tm n} :
    substitute σ (weaken ρ t) = substitute (comp_substitute_weaken σ ρ) t :=
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
