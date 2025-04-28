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

-- macros for easier usage of de bruijn abstractions

macro "context_info_nat_relations" : tactic =>
  `(tactic|
      (first
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

macro "conversion_var_sub_symm" : tactic =>
  `(tactic|
    (
      apply Eq.symm
      apply conversion_var_substitute
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

macro "substitution_var_substitute_id" : tactic =>
  `(tactic|
    (
      apply substitution_var_substitute_id
      intro x
      cases' x with i hFin
      cases' i with i'
     ))

macro "substitution_var_substitute_id_symm" : tactic =>
  `(tactic|
    (
      apply Eq.symm
      apply substitution_var_substitute_id
      intro x
      cases' x with i hFin
      cases' i with i'
     ))

macro "weakening_var_weaken_id" : tactic =>
  `(tactic|
    (
      apply weakening_var_weaken_id
      intro x
      cases' x with i hFin
      cases' i with i'
     ))

macro "weakening_var_weaken_id_symm" : tactic =>
  `(tactic|
    (
      apply Eq.symm
      apply weakening_var_weaken_id
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

-- meta cases tactic from ITP lecture
def cases (id : FVarId) : TacticM Unit :=
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
          if Expr.isAppOfArity (LocalDecl.type ldecl) ``Eq 3 then
            try
              cases (LocalDecl.fvarId ldecl)
            catch _ =>
              logInfo m!"error on case: {ldecl.type}, stopping here"
              return
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
        try conversion_var_sub_symm
        try substitution_var_substitute_id
        try substitution_var_substitute_id_symm
        try weakening_var_weaken_id
        try weakening_var_weaken_id_symm
        try substitution_from_composition
        try simp []
        try split_and_cases
        try simp []
        try repeat' apply And.intro
        try any_goals rfl
        ))

elab "fail_if_no_target_change " tac:tacticSeq : tactic => do
  let goalsBefore ← getGoals
  let goalTypesBefore ← goalsBefore.mapM fun g => g.getType

  try
    evalTactic tac
  catch _ =>
    throwError "Inner tactic failed."

  let goalsAfter ← getGoals
  let goalTypesAfter ← goalsAfter.mapM fun g => g.getType

  if goalTypesBefore == goalTypesAfter then
    throwError "Tactic did not change the goal state."

macro "substitution_norm" : tactic =>
  `(tactic| (repeat' (fail_if_no_target_change substitution_step)))

-- to be used, when either part of the equation contains metavariables
macro "substitution_step_meta" : tactic =>
  `(tactic|
      (
        try substitution_to_composition
        try substitution_nat_relation_lemmatas
        try simp []
        try substitution_from_composition
        try simp []
        try split_and_cases
        try simp []
        try repeat' apply And.intro
        try any_goals rfl
        ))
