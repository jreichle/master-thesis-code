import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Conversion
import IMLTT.untyped.proofs.Composition

import Mathlib.Tactic.Cases
import Mathlib.Tactic.FailIfNoProgress

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

-- use macros

macro "context_info_nat_relations" : tactic =>
  `(tactic|
      (first -- FIXME: find way to do all lemmatas for all available contexts (repeat' not possible)
        | have := by
            apply gen_ctx_leq
            assumption
        | have := by
            apply gen_ctx_leq_sub
            assumption
        | have := by
            apply gen_ctx_neq
            assumption
        | have := by
            apply gen_ctx_nil
            assumption
      ))

macro "substitution_nat_relation_lemmatas" : tactic =>
  `(tactic|
      (
        try context_info_nat_relations
        (repeat' first
          | rw [←lift_weaken_from]
            any_goals omega
          | rw [weaken_from_zero]
            any_goals omega
          | rw [←lift_n_substitution]
            any_goals omega
          | rw [n_substitution_zero]
            any_goals omega
          | rw [←lift_n_substitution_shift]
            any_goals omega
          | rw [n_substitution_shift_zero]
            any_goals omega
          | rw [zero_substitution]
            any_goals omega
          )
      ))

macro "substitution_to_composition" : tactic =>
  `(tactic|
      (repeat' first
        | simp only [weakening_comp]
        | simp only [weakening_var_comp]
        | simp only [substitution_comp]
        | simp only [substitution_var_comp]
        | simp only [substitution_comp_σρ]
        | simp only [substitution_var_comp_σρ]
        | simp only [substitution_comp_ρσ]
        | simp only [substitution_var_comp_ρσ]
        ))

macro "substitution_from_composition" : tactic =>
  `(tactic|
      (repeat' first
        | simp only [←weakening_comp]
        | simp only [←weakening_var_comp]
        | simp only [←substitution_comp]
        | simp only [←substitution_var_comp]
        | simp only [←substitution_comp_σρ]
        | simp only [←substitution_var_comp_σρ]
        | simp only [←substitution_comp_ρσ]
        | simp only [←substitution_var_comp_ρσ]
        ))

macro "substitution_var_sub" : tactic =>
  `(tactic|
    (
      apply substitution_var_substitute
      intro x
      cases' x with i hFin
      cases' i with i'
     ))

macro "weakening_var_weak" : tactic =>
  `(tactic|
    (
      apply weakening_var_weaken
      intro x
      cases' x with i hFin
      cases' i with i'
     ))

macro "conversion_var_sub" : tactic =>
  `(tactic|
    (
      apply conversion_var_substitute
      intro x
      cases' x with i hFin
      cases' i with i'
     ))

macro "substitution_split" : tactic =>
  `(tactic|
    (
      split
      case h_1 heq =>
        cases heq
      case h_2 heq =>
        cases heq
     ))


def cases (id : FVarId) : TacticM Unit := -- XXX: aus interactive theorem proving repo
  do
    liftMetaTactic (fun goal ↦
      do
        let subgoals ← MVarId.cases goal id
        pure (List.map (fun subgoal ↦
            InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
          (Array.toList subgoals)))

partial def useCases : TacticM Unit :=
  withMainContext
    (do
       let lctx ← getLCtx
       for ldecl in lctx do
         if ! LocalDecl.isImplementationDetail ldecl then
           if Expr.isAppOfArity (LocalDecl.type ldecl) ``Eq 3
            then -- FIXME: how to abort, if dependent elimination breaks this? e.g. on cases heqΓ
                 -- use simple try block?
              cases (LocalDecl.fvarId ldecl)
              -- return
    )

elab "use_cases" : tactic =>
  useCases


macro "split_and_cases" : tactic =>
  `(tactic|
      (split
       any_goals use_cases))

macro "substitution_step" : tactic =>
  `(tactic|
      (
        try substitution_to_composition
        try substitution_nat_relation_lemmatas
        try simp []
        try substitution_var_sub
        try weakening_var_weak
        try conversion_var_sub
        try substitution_from_composition
        try simp []
        try split_and_cases
        try simp []
        try repeat' apply And.intro
        try any_goals rfl
        ))

macro "substitution_norm" : tactic => -- FIXME: still infinite, because haves, needs if_goal_unchanged
  `(tactic|
      (
        repeat' (fail_if_no_progress substitution_step)
        ))




-- FIXME: change al theorems to not use ⌈-⌉₀ anymore? or add simp ones

theorem weak_sub_zero :
    t⌈a⌉₀⌊ρ⌋ = t⌊⇑ₚρ⌋⌈a⌊ρ⌋⌉₀ :=
  by
    substitution_norm

theorem weak_sub_shift :
    t⌈(ₛ↑ₚidₚ), a⌉⌊⇑ₚρ⌋ = t⌊⇑ₚρ⌋⌈(ₛ↑ₚidₚ), (a⌊⇑ₚρ⌋)⌉ :=
  by
    substitution_norm

theorem substitution_var_single_comp :
    v(x)⌈(ₛidₚ), a ₛ∘ₛ⇑ₛσ⌉ = v(x)⌈σ, a⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_single_comp :
    t⌈(ₛidₚ), a ₛ∘ₛ⇑ₛσ⌉ = t⌈σ, a⌉ :=
  by
    substitution_norm

@[simp]
theorem weakening_var_comp_id :
    x⌊ρ ₚ∘ₚidₚ⌋ᵥ = x⌊ρ⌋ᵥ :=
  by
    simp [←weakening_var_comp]

@[simp]
theorem weakening_comp_id :
    t⌊ρ ₚ∘ₚidₚ⌋ = t⌊ρ⌋ :=
  by
    simp [←weakening_comp]

@[simp]
theorem substitution_var_comp_id :
    x⌈(ₛidₚ)ₛ∘ₛσ⌉ᵥ = x⌈σ⌉ᵥ :=
  by
    simp [←substitution_var_comp]

@[simp]
theorem substitution_comp_id :
    t⌈(ₛidₚ)ₛ∘ₛσ⌉ = t⌈σ⌉ :=
  by
    simp [←substitution_comp]

@[simp]
theorem substitution_var_comp_σρ_id :
    x⌈(ₛidₚ) ₛ∘ₚρ⌉ᵥ = x⌊ρ⌋ᵥ :=
  by
    simp [←substitution_var_comp_σρ]

@[simp]
theorem substitution_comp_σρ_id :
    t⌈(ₛidₚ) ₛ∘ₚρ⌉ = t⌊ρ⌋ :=
  by
    simp [←substitution_comp_σρ]

@[simp]
theorem substitution_var_comp_ρσ_id :
    x⌈ρ ₚ∘ₛ(ₛidₚ)⌉ᵥ = x⌊ρ⌋ᵥ :=
  by
    simp [←substitution_var_comp_ρσ]

@[simp]
theorem substitution_comp_ρσ_id :
    t⌈ρ ₚ∘ₛ(ₛidₚ)⌉ = t⌊ρ⌋ :=
  by
    simp [←substitution_comp_ρσ]

@[simp]
theorem substitution_extend :
    t⌈⇑ₛσ⌉⌈a⌉₀ = t⌈σ, a⌉ :=
  by
    substitution_norm

theorem substitution_extend_lift :
    t⌈⇑ₛσ⌉⌊⇑ₚρ⌋⌈a⌉₀ = t⌈ρ ₚ∘ₛσ, a⌉ :=
  by
    substitution_norm

@[simp]
theorem substitution_zero_lift :
    t⌈a⌉₀⌈σ⌉ = t⌈⇑ₛσ⌉⌈a⌈σ⌉⌉₀ :=
  by
    substitution_norm

@[simp]
theorem idWkLiftSubstLemma :
    t⌈⇑ₛσ⌉⌊⇑ₚ↑ₚidₚ⌋⌈v(0)⌉₀ = t⌈⇑ₛσ⌉ :=
  by
    substitution_norm

theorem singleSubstLift :
    t⌈(ₛ↑ₚidₚ), a⌉⌈⇑ₛσ⌉ = t⌈⇑ₛσ⌉⌈(ₛ↑ₚidₚ), (a⌈⇑ₛσ⌉)⌉ :=
  by
    substitution_norm

-- own
theorem lift_single_subst_tt :
   A⌊⇑ₚweaken_from n l⌋⌈⋆⌉₀ = A⌈⋆⌉₀⌊weaken_from n l⌋ :=
  by
    substitution_norm

theorem substitution_shift_substitute_zero :
    A⌊↑ₚidₚ⌋⌈s⌉₀ = A :=
  by
    substitution_norm

@[simp]
theorem substitution_shift_substitute_zero_simp :
    A⌊↑ₚidₚ⌋⌈(ₛidₚ), s⌉ = A :=
  by
    substitution_norm

theorem substitution_twice_zero {n : Nat} {T : Tm (n + 2)} {b : Tm (n)} {a : Tm (n)} :
    T⌈(ₛidₚ), a, b⌉ = T⌈b⌊↑ₚidₚ⌋⌉₀⌈a⌉₀ :=
  by
    substitution_norm

theorem substitution_separate {n m : Nat} {t : Tm (n + 1)} {s : Tm m} {σ : Subst m n} :
    t⌈σ, s⌉ = t⌈⇑ₛσ⌉⌈s⌉₀ :=
  by
    substitution_norm

@[simp]
theorem substitution_weak_id : -- TODO: can be generalized to v(i)
    B⌈(ₛ↑ₚ↑ₚidₚ), v(1)⌉ = B⌊↑ₚidₚ⌋ :=
  by
    rw (config := {occs := .pos [2]}) [←substitution_id (t := B)]
    substitution_to_composition
    substitution_var_sub
    any_goals substitution_step

theorem weak_substitution_eq_weakening_substitution {l m : Nat} {leq : (l + 1) ≤ m} {S : Tm m} {s : Tm (l + 1)}:
    S⌊↑₁m↬l⌋⌈s/ₙ(leq)⌉ = S⌈s↑/ₙ(leq)⌉ :=
  by
    induction m with
    | zero =>
      substitution_step
    | succ m' ih =>
      substitution_step
      · cases m' with
        | zero =>
          substitution_step
        | succ n =>
          unfold n_substitution
          split
          case isTrue =>
            substitution_step
          case isFalse =>
            unfold n_substitution_shift
            split
            case isTrue =>
              substitution_step
            case isFalse =>
              substitution_step
      · cases m' with
        | zero =>
          substitution_step
        | succ n =>
          unfold n_substitution
          split
          case isTrue =>
            substitution_step
            · simp only [←substitution_conv_var]
              rw [←ih]
              substitution_step
            · simp only [←substitution_conv_var]
              rw [←ih]
              substitution_step
          case isFalse =>
            unfold n_substitution_shift
            split
            case isTrue =>
              substitution_step
            case isFalse =>
              substitution_step

theorem weak_substitution_eq_weakening_substitution_gen_context {l n : Nat} {s : Tm (l + 1)} {Δ : CtxGen (l + 1) n} :
    ⌈s⌉(⌊↑₁↬l⌋Δ w/(Nat.le_refl (l + 1))) = ⌈s↑⌉(Δ w/(Nat.le_refl (l + 1))) :=
  by
    induction Δ with
    | start =>
      simp [weaken_from_into_gen_ctx]
      simp [substitute_into_gen_ctx]
      simp [substitute_shift_into_gen_ctx]
    | expand Δ' S' ih =>
      simp [weaken_from_into_gen_ctx]
      simp [substitute_into_gen_ctx]
      simp [substitute_shift_into_gen_ctx]
      apply And.intro
      · rw [ih]
      · rw [weak_substitution_eq_weakening_substitution]
