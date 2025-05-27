import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Mixture

import IMLTT.untyped.Macros

import IMLTT.typed.JudgmentsAndRules

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

-- elab "apply_replace_meta" nameIdent:ident : tactic =>
--   let tryApplyType (ty : Expr) : TacticM Unit := do
--     let (_, _, resultType) ← forallMetaTelescope ty
--     liftMetaTactic (fun goal => MVarId.apply goal resultType)
-- 
--   withMainContext (do
--     try
--       let name ← resolveGlobalConstNoOverload nameIdent
--       let env ← getEnv
--       match env.find? name with
--       | some constInfo => 
--         tryApplyType constInfo.type
--       | none => logInfo m!"replacing - not found in env"
--     catch _ =>
--       let lctx ← getLCtx
--       match lctx.findFromUserName? nameIdent.getId with
--       | some lname =>
--         match lctx.find? (lname.fvarId) with
--         | some constInfo => tryApplyType constInfo.type
--         | none => logInfo m!"replacing - not found in lctx"
--       | none => logInfo m!"replacing - decl not found from user name"
--     )
-- 
-- elab "apply_from_name" nameIdent:ident : tactic =>
--   withMainContext
--     (do -- FIXME: try with syntax:stx and evalApply, elabTermForApply
-- 
--       -- let goals ← getGoals
--       -- let mut goal := none
--       -- for g in goals do
--       --   let tag ← g.getTag
--       --   if tag.eqStr "prf" then goal := some g
--       try
--         let name ← resolveGlobalConstNoOverload nameIdent
--         let cst ← mkConstWithFreshMVarLevels name
--         liftMetaTactic (fun goal ↦ MVarId.apply goal cst)
--       catch _ =>
--         let lctx ← getLCtx
--         match lctx.findFromUserName? nameIdent.getId with
--         | some lname =>
--           liftMetaTactic (fun goal ↦ MVarId.apply goal (.fvar lname.fvarId))
--         | none => logInfo m!"applying - decl not found from user name"
--       )
-- 
-- -- elab "congr_to_arity" : tactic => do
-- --   let target ← getMainTarget
-- --   match target.eq? with
-- --   | some (_, lhs, rhs) =>
-- --     let rec applyCongr n :=
-- --       if n ≤ 0 then pure ()
-- --       else do evalTactic (← `(tactic| apply congr)) *> applyCongr (n - 1)
-- --     applyCongr (lhs.getAppNumArgs - 1)
-- --   | none => throwError "Goal is not an equality between two terms"
-- 
-- macro "replace_by_conclusion" nameIdent:ident : tactic =>
--   `(tactic|
--     (
--       apply replaceWithEq
--       rotate_right
--       apply_replace_meta $nameIdent;
--       rotate_right; rotate_right
--      ))
-- 
-- macro "apply_subst_eq" nameIdent:ident : tactic =>  -- XXX: term instead of ident? any way to do .var hA in one
--   `(tactic|
--     (
--       apply replaceWithEq
--       rotate_right
--       apply_replace_meta $nameIdent
--       rotate_right; rotate_right
--       congr 1
--       try any_goals solve | substitution_norm_meta
--       try any_goals solve | substitution_norm
--       try any_goals apply_from_name $nameIdent
--     )
--   )

elab "apply_replace_meta" tm:term : tactic =>
  withMainContext do
    -- to @tm (make implicit parameters explicit)
    let atTm ← elabTermForApply tm
    let inferredType ← inferType atTm
    -- cut out and use only conclusion, replace quantified parameters with metavars
    -- ∀α β f, f α → f β to ?f ?β
    let (_, _, resultType) ← forallMetaTelescope inferredType
    liftMetaTactic fun goal => MVarId.apply goal resultType

elab "apply_to_prf" tm:term : tactic =>
  withMainContext do
    let goals ← getGoals
    for goal in goals do
      let tag ← goal.getTag
      if tag.toString.endsWith "prf" then
        let t ← goal.getType
        logInfo m!"found {t}"
        let atTm ← elabTermForApply tm
        liftMetaTactic fun _ => goal.apply atTm -- not sound
        return

-- colGt only reads to real line break (exluding indented)
macro "apply_subst_eq" colGt tm:term : tactic =>
  `(tactic|
    (
      apply replaceWithEq
      rotate_right
      apply_replace_meta $tm
      rotate_right; rotate_right
      congr 1 -- Γ ⊢ A type = Γ' ⊢ A' type to Γ = Γ' and A = A'
      try any_goals solve | substitution_norm_meta
      try any_goals solve | substitution_norm
      -- apply_to_prf $tm
      try any_goals apply $tm
    )
  )


-- theorem test_eq_thing_thm {n : Nat} {Γ : Ctx n} {A : Tm n}:
--     Γ ⊢ A type → Γ ⬝ A ⊢ v(0) ∶ A⌈ₛidₚ⌉⌊↑ₚidₚ⌋ :=
--   by
--     intro hA
--     apply replaceWithEq
--     rotate_left
--     apply HasType.var
--     rotate_right
--     substitution_norm
--     apply hA
-- 
-- theorem test_eq_thing_mac {n : Nat} {Γ : Ctx n} {A : Tm n}:
--     Γ ⊢ A type → Γ ⬝ A ⊢ v(0) ∶ A⌈ₛidₚ⌉⌊↑ₚidₚ⌋ :=
--   by
--     intro hA
--     apply replaceWithEq
--     rotate_right
--     apply_replace_meta HasType.var
--     rotate_right; rotate_right
--     substitution_norm
--     apply_subst_eq HasType.var
--     apply hA
-- 
-- theorem test_eq_thing' {n : Nat} {Γ : Ctx n} {A : Tm n}:
--     Γ ⊢ A type → Γ ⬝ A ⊢ v(0) ∶ A⌈ₛidₚ⌉⌊↑ₚidₚ⌋ :=
--   by
--     intro hA
--     apply_subst_eq HasType.var
--     apply hA
-- 
-- 
-- theorem inhabitant_pi_same_type_diff_val' :
--     (Γ ⬝ A ⊢ P type)
--     → (Γ ⬝ A ⊢ λP;v(0) ∶ (Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(0)⌉⌊↑ₚidₚ⌋))⌈(ₛidₚ)⋄ v(0)⌉) :=
--   by
--     intro hP
--     have h := HasType.pi_intro (HasType.var hP)
--     apply_subst_eq HasType.pi_intro (HasType.var hP)
-- 
-- theorem weakening_pi_intro' :
--     ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
--     (Γ ⬝ A ⊢ b ∶ B)
--     → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
--       Γ_1 ⊢ S type
--       → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
--       → eqM ▸ b = a
--       → eqM ▸ B = A_1
--       → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
--     → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
--     Γ_1 ⊢ S type
--     → eqM ▸ Γ = Γ_1 ⊗ Δ
--     → (eqM ▸ λA; b) = a
--     → (eqM ▸ ΠA;B) = A_1
--     → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
--   by
--     intro n Γ' A b B hbB ihbB m l Γ Δ heqM S t T hS heqΓ heqt heqT
--     cases heqM
--     cases heqΓ
--     cases heqt
--     cases heqT
--     apply HasType.pi_intro
--     apply replaceWithEq
--     any_goals sorry
--     -- apply_to_prf ihbB
--     -- rotate_right
--     -- congr 1
--     -- rw [←extend_expand_context_weaken_from]
--     -- substitution_norm
--     -- apply hS
--     --
--     -- apply_subst_eq ihbB
--     -- rw [←extend_expand_context_weaken_from]
--     -- apply hS
--     -- repeat' rfl
--     --
-- theorem weakening_pi_intro''' :
--     ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
--     (Γ ⬝ A ⊢ b ∶ B)
--     → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
--       Γ_1 ⊢ S type
--       → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
--       → eqM ▸ b = a
--       → eqM ▸ B = A_1
--       → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
--     → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
--     Γ_1 ⊢ S type
--     → eqM ▸ Γ = Γ_1 ⊗ Δ
--     → (eqM ▸ λA; b) = a
--     → (eqM ▸ ΠA;B) = A_1
--     → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
--   by
--     intro n Γ' A b B hbB ihbB m l Γ Δ heqM S t T hS heqΓ heqt heqT
--     cases heqM
--     cases heqΓ
--     cases heqt
--     cases heqT
--     apply HasType.pi_intro
--     apply replaceWithEq
--     rotate_right
--     apply_replace_meta ihbB
--     rotate_right; rotate_right
--     congr 1
--     · rw [←extend_expand_context_weaken_from]
--     · substitution_norm
--     · substitution_norm
--     apply ihbB
--     apply hS
--     repeat' rfl
-- 
-- theorem weakening_var' :
--     ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
--     Γ ⊢ A type
--     → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (A_1 : Tm m),
--       Γ_1 ⊢ S type
--       → eqM ▸ Γ = Γ_1 ⊗ Δ
--       → eqM ▸ A = A_1
--       → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
--     → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x + 1 = m) (S : Tm l) (a A_1 : Tm m),
--     Γ_1 ⊢ S type
--     → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
--     → eqM ▸ v(0) = a
--     → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
--     → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
--   by
--     intro n Γ A hA ihA m l Γ Δ heqM S t T hS heqΓ heqt heqT
--     cases heqM
--     cases heqt
--     cases heqT
--     cases Δ with
--     | start =>
--       cases heqΓ
--       apply_subst_eq HasType.weak (HasType.var hA) hS
--     | expand Δ' S' =>
--       cases heqΓ
--       apply_subst_eq HasType.var
--       apply ihA
--       apply hS
--       any_goals rfl
