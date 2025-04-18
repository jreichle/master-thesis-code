import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules

import Mathlib.Tactic.FailIfNoProgress

theorem useVarwithWeak :
    Γ ⊢ A type → A⌊↑ₚidₚ⌋ = B → Γ ⬝ A ⊢ v(0) ∶ B :=
  by
    intro hA hEq
    cases hEq
    apply HasType.var
    apply hA

theorem useWeakwithWeak :
    (Γ ⊢ v(i) ∶ A) → Γ ⊢ B type → v(i)⌊↑ₚidₚ⌋ = v(j) → A⌊↑ₚidₚ⌋ = A' → Γ ⬝ B ⊢ v(j) ∶ A' :=
  by
    intro hvA hB hEqv heqA
    cases hEqv
    cases heqA
    rw [←weaken]
    apply HasType.weak
    · apply hvA
    · apply hB

theorem use_equality_ctx {n : Nat} {Γ Δ : Ctx n}
    (hiC : Δ ctx) (heqΓ : Γ = Δ) :
    Γ ctx :=
  by
    simp_all

theorem use_equality_type {n : Nat} {Γ Δ : Ctx n} {A B : Tm n}
    (hB : Δ ⊢ B type) (heqΓ : Γ = Δ) (heqB : A = B) :
    Γ ⊢ A type :=
  by
    simp_all

theorem use_equality_term {n : Nat} {Γ Δ : Ctx n} {A B a b : Tm n}
    (hbB : Δ ⊢ b ∶ B) (heqΓ : Γ = Δ) (heqa : a = b) (heqA : A = B) :
    Γ ⊢ a ∶ A :=
  by
    simp_all

theorem use_equality_type_eq {n : Nat} {Γ Δ : Ctx n} {A B A' B' : Tm n}
    (hBB : Δ ⊢ B ≡ B' type) (heqΓ : Γ = Δ) (heqA : A = B) (heqA' : A' = B') 
    : Γ ⊢ A ≡ A' type :=
  by
    simp_all

theorem use_equality_term_eq {n : Nat} {Γ Δ : Ctx n} {A B a b a' b' : Tm n}
    (hBB : Δ ⊢ b ≡ b' ∶ B) (heqΓ : Γ = Δ) (heqa : a = b) (heqa' : a' = b') (heqA : A = B)
    : Γ ⊢ a ≡ a' ∶ A :=
  by
    simp_all

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

theorem replaceWithEq {goal repl : Prop} (eq : repl = goal) (prf : repl) :
    goal :=
  by
    cases eq
    refine prf

def replaceWithEqApply (nameIdent : TSyntax `ident) : TacticM Unit :=
  withMainContext
    (do
      try -- FIXME: find better solution that try-catch
        let name ← resolveGlobalConstNoOverload nameIdent
        let env ← getEnv
        match env.find? name with
        | some constInfo =>
          let reduced_type ← forallMetaTelescope constInfo.type
          liftMetaTactic (fun goal ↦ MVarId.apply goal reduced_type.snd.snd)
        | none => 
          logInfo m!"not found in env"
      catch _ =>
        let lctx ← getLCtx
        let userName := nameIdent.getId
        match lctx.findFromUserName? userName with
        | some lname =>
          match lctx.find? (lname.fvarId) with
          | some constInfo =>
            let reduced_type ← forallMetaTelescope constInfo.type
            liftMetaTactic (fun goal ↦ MVarId.apply goal reduced_type.snd.snd)
          | none =>
            logInfo m!"not found in ctx"
        | none =>
          logInfo m!"decl not found from user name"
      )

elab "replace_with_eq_apply" nameIdent:ident : tactic =>
  replaceWithEqApply nameIdent

macro "replace_by_conclusion" nameIdent:ident : tactic =>
  `(tactic|
    (
      apply replaceWithEq -- FIXME: problems if more than one open goal
      rotate_right
      replace_with_eq_apply $nameIdent; skip
      rotate_right
      rotate_right
     ))

      -- XXX: new tactics that:
      -- - apply congr to the equation until no change? and apply substitution_step automatically?
      -- - apply given theorem immediately?
      -- - new tactic, that takes in hypthesis and symplifies it

theorem test_eq_thing' {n : Nat} {Γ : Ctx n} {A : Tm n}:
    Γ ⊢ A type → Γ ⬝ A ⊢ v(0) ∶ A⌈ₛidₚ⌉⌊↑ₚidₚ⌋ :=
  by
    intro hA
    replace_by_conclusion HasType.var
    · substitution_step
    · apply HasType.var hA
