import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution

theorem substitution_conv_var :
    v(x)⌈σ⌉ = x⌈σ⌉ᵥ :=
  by
    simp [substitute]

theorem substitution_conv_zero :
    t⌈(ₛidₚ), σ⌉ = t⌈σ⌉₀ :=
  by
    simp [substitute_zero]

theorem zero_substitution_conv :
    t⌈(ₛidₚ), σ⌉ = t⌈σ/₀⌉ :=
  by
    simp [zero_substitution]

theorem conversion_var_lift :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌊ρ⌋) → ∀ (x : Fin (n + 1)), v(x)⌈⇑ₛσ⌉ = v(x)⌊⇑ₚρ⌋ :=
  by
    intro h x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        rfl
      | succ i' =>
        apply congrArg shift_tm (h (.mk i' (Nat.lt_of_succ_lt_succ hFin)))

theorem conversion_var_lift_n :
    (∀x, v(x)⌈σ⌉ = v(x)⌊ρ⌋) → ∀x, v(x)⌈l ₙ⇑ₛσ⌉ = v(x)⌊l ₙ⇑ₚρ⌋ :=
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
          apply conversion_var_lift
          apply conversion_var_lift_n
          apply h

theorem conversion_var_substitute {σ σ' : Subst m n} :
    (∀x, v(x)⌈σ⌉ = v(x)⌊ρ⌋) → ∀t, t⌈σ⌉ = t⌊ρ⌋ :=
  by
    intro h t
    match t with
    | .unit =>
      simp [substitute]
      simp [weaken]
    | .empty =>
      simp [substitute]
      simp [weaken]
    | .pi A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
    | .sigma A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
    | .nat =>
      simp [substitute]
      simp [weaken]
    | .iden A a a' =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply And.intro
        · apply conversion_var_substitute h
          assumption
        · apply conversion_var_substitute h
          assumption
    | .univ =>
      simp [substitute]
      simp [weaken]
    | .var x =>
      apply h
    | .tt =>
      simp [substitute]
      simp [weaken]
    | .indUnit A b a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply And.intro
        · apply conversion_var_substitute h
          assumption
        · apply conversion_var_substitute h
          assumption
    | .indEmpty A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply conversion_var_substitute h
        assumption
    | .lam A b => 
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
    | .app f a => 
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute h
        assumption
    | .pairSigma a b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute h
        assumption
    | .firstSigma p =>
      simp [substitute]
      simp [weaken]
      apply conversion_var_substitute h
      assumption
    | .secondSigma p =>
      simp [substitute]
      simp [weaken]
      apply conversion_var_substitute h
      assumption
    | .zeroNat =>
      simp [substitute]
      simp [weaken]
    | .succNat i =>
      simp [substitute]
      simp [weaken]
      apply conversion_var_substitute h
      assumption
    | .indNat A z s i =>
      simp [substitute]
      simp [weaken]
      repeat' apply And.intro
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 2 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply conversion_var_substitute h
        assumption
    | .refl A a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute h
        assumption
    | .j A B b a a' p => 
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply And.intro
        · apply conversion_var_substitute
          · have ξ := lift_subst_n 3 σ
            apply ξ
          · apply conversion_var_lift_n h
        · apply And.intro
          · apply conversion_var_substitute h
            assumption
          · apply And.intro
            · apply conversion_var_substitute h
              assumption
            · apply And.intro
              · apply conversion_var_substitute h
                assumption
              · apply conversion_var_substitute h
                assumption

theorem conversion_var_sub_weak :
    v(x)⌈ₛρ⌉ = v(x)⌊ρ⌋ :=
  by
    simp [substitute]
    simp [substitute_var]

theorem conversion_sub_weak :
    t⌈ₛρ⌉ = t⌊ρ⌋ :=
  by
    cases t with
    | unit =>
      simp [substitute]
      simp [weaken]
    | empty =>
      simp [substitute]
      simp [weaken]
    | pi A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
    | sigma A B =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
    | nat =>
      simp [substitute]
      simp [weaken]
    | iden A a a' =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply And.intro
        · apply conversion_sub_weak
        · apply conversion_sub_weak
    | univ =>
      simp [substitute]
      simp [weaken]
    | var x =>
      apply conversion_var_sub_weak
    | tt =>
      simp [substitute]
      simp [weaken]
    | indUnit A b a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply And.intro
        · apply conversion_sub_weak
        · apply conversion_sub_weak
    | indEmpty A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply conversion_sub_weak
    | lam A b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
    | app f a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_sub_weak
    | pairSigma a b =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_sub_weak
    | firstSigma p =>
      simp [substitute]
      simp [weaken]
      apply conversion_sub_weak
    | secondSigma p =>
      simp [substitute]
      simp [weaken]
      apply conversion_sub_weak
    | zeroNat =>
      simp [substitute]
      simp [weaken]
    | succNat i =>
      simp [substitute]
      simp [weaken]
      apply conversion_sub_weak
    | indNat A z s i =>
      simp [substitute]
      simp [weaken]
      repeat' apply And.intro
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 2 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply conversion_sub_weak
    | refl A a =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_sub_weak
    | j A B b a a' p =>
      simp [substitute]
      simp [weaken]
      apply And.intro
      · apply conversion_sub_weak
      · apply And.intro
        · apply conversion_var_substitute
          · apply lift_subst_n 3 (.weak ρ)
          · apply conversion_var_lift_n
            apply conversion_var_sub_weak
        · apply And.intro
          · apply conversion_sub_weak
          · apply And.intro
            · apply conversion_sub_weak
            · apply And.intro
              · apply conversion_sub_weak
              · apply conversion_sub_weak

theorem substitution_conv_shift :
    x⌈ₛ↑ₚρ⌉ᵥ = x⌈↑ₛ(ₛρ)⌉ᵥ :=
  by
    simp [substitute_var]
    simp [shift_tm]
    rfl

theorem substitution_conv_shift_term :
    t⌈ₛ↑ₚρ⌉ = t⌈↑ₛ(ₛρ)⌉ :=
  by
    apply substitution_var_substitute
    intro x
    simp [substitute]
    simp [substitute_var]
    simp [shift_tm]
    rfl

theorem substitution_conv_shift_id_conv :
    t⌈ₛ↑ₚidₚ⌉ = t⌊↑ₚidₚ⌋ :=
  by
    apply conversion_var_substitute
    · apply ₛ↑ₚidₚ
    · intro x
      simp [substitute]
      simp [substitute_var]

theorem substitution_conv_shift_comp_ρσ :
    ↑ₚρ ₚ∘ₛ (σ, t) = ↑ₛ(ρ ₚ∘ₛ σ, (t⌊ρ⌋)) :=
  by
    simp [comp_weaken_substitute]

theorem substitution_var_conv_shift_id {σ : Subst m n} {x : Fin n} :
    x⌈σ⌉ᵥ⌊↑ₚidₚ⌋ = x⌈↑ₛσ⌉ᵥ :=
  by
    simp [substitute_var]
    rfl

theorem substitution_conv_comp_ρρ :
    x⌊ρ ₚ∘ₚ ρ'⌋ᵥ = x⌈ρ ₚ∘ₛ (ₛρ')⌉ᵥ :=
  by
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [comp_weaken]
      simp [substitute_var]
      simp [weaken]
    | shift ξ =>
      simp [comp_weaken_substitute]
      simp [comp_weaken]
      simp [substitute_var]
      simp [weaken]
    | lift ξ =>
      simp [comp_weaken_substitute]
      simp [comp_weaken]
      simp [substitute_var]
      simp [weaken]
