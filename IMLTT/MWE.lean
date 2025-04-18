import Mathlib.Tactic.Convert

-- inductive Tm : Nat → Type where
--   | unit : Tm n
--   | pi : Tm n → Tm (n + 1) → Tm n
--   | lam : Tm n → Tm (n + 1) → Tm n
--   | var : Fin n → Tm n
-- 
-- inductive Ctx : Nat → Type where
--   | empty : Ctx 0
--   | extend : Ctx n → Tm n → Ctx (n + 1)
-- 
-- inductive Weak : Nat → Nat → Type where
--   | id : Weak n n
--   | shift : Weak m n → Weak (m + 1) n
--   | lift : Weak m n → Weak (m + 1) (n + 1)
-- 
-- def weaken_var (ρ : Weak m n) (x : Fin n) : Fin m :=
--   match ρ with
--   | .id => x
--   | .shift ρ => .succ (weaken_var ρ x)
--   | .lift ρ =>
--     match x with
--     | ⟨0, _⟩ => 0
--     | ⟨x' + 1, h⟩ => .succ (weaken_var ρ (Fin.mk x' (Nat.lt_of_succ_lt_succ h)))
-- 
-- def weaken (ρ : Weak m n) (t : Tm n) : Tm m :=
--   match t with
--   | .unit => .unit
--   | .pi A B => .pi (weaken ρ A) (weaken (.lift ρ) B)
--   | .var i => .var (weaken_var ρ i)
--   | .lam A b => .lam (weaken ρ A) (weaken (.lift ρ) b)
-- 
-- mutual
--   inductive IsCtx : Ctx n → Prop where
--     | empty : IsCtx .empty
--     | extend : IsCtx Γ → IsType Γ A → IsCtx (.extend Γ A)
-- 
--   inductive IsType : Ctx n → Tm n → Prop where
--     | unit_form : IsCtx Γ
--                   → IsType Γ .unit
--     | pi_form : IsType Γ A → IsType (.extend Γ A) B
--                 → IsType Γ (.pi A B)
-- 
--   inductive HasType : Ctx n → Tm n → Tm n → Prop where
--     | var :
--       IsType Γ A
--       → HasType (.extend Γ  A) (.var 0) (weaken (.shift .id) A)
--     | weak :
--       HasType Γ (.var x) A → IsType Γ B
--       → HasType (.extend Γ B) (weaken (.shift .id) (.var x)) (weaken (.shift .id) A)
--     | pi_intro :
--       HasType (.extend Γ A) b B
-- end
-- 
-- theorem almost_var :
--     IsType Γ A → HasType (.extend Γ A) (.var (0)) (weaken (.shift .id) (weaken .id A)) :=
--   by
--     intro h₁
--     convert_to (HasType (.extend Γ A) (.var (0)) (?t)) -- does nothing
--     -- apply HasType.var
--     sorry

-- more abstract

inductive Tm : Nat → Type where
  | unit : Tm n
  | var : Fin n → Tm n

inductive Ctx : Nat → Type where
  | empty : Ctx 0
  | extend : Ctx n → Tm n → Ctx (n + 1)

inductive Op : Nat → Nat → Type where
  | id : Op n n
  | incr : Op m n → Op (m + 1) n

def op_var (ρ : Op m n) (x : Fin n) : Fin m :=
  match ρ with
  | .id => x
  | .incr ρ => .succ (op_var ρ x)

def op (ρ : Op m n) (t : Tm n) : Tm m :=
  match t with
  | .unit => .unit
  | .var i => .var (op_var ρ i)

inductive IndProp : Ctx n → Tm n → Prop where
  | var : IndProp (.extend Γ  A) (op (.incr .id) A)

theorem replaceWithEq {goal repl : Prop} (eq : repl = goal) (prf : repl) :
    goal :=
  by
    cases eq
    refine prf

theorem almost_var_manual :
    IndProp (.extend Γ A) (op (.incr .id) (op .id A)) :=
  by
    apply replaceWithEq (repl := IndProp (Ctx.extend ?Γ ?A) (op Op.id.incr ?A))
    · sorry
    · apply IndProp.var
    repeat' assumption

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

def replaceWithEqApply : TacticM Unit :=
  withMainContext
    (do
      let origGoals ← getGoals
      let origMainGoal ← getMainGoal
      let origMainGoalType ← origMainGoal.getType
      logInfo m!"main goal type: {origMainGoalType}"

      -- thm or ind-prop constructor that is to be applied
      -- might be useful: Lean.Meta.inferType expr
      let name := ``IndProp.var -- TODO: adjust to be function parameter
      let env ← getEnv
      match env.find? name with
      | some constInfo =>
        -- get conclusion of thm
        let ty := constInfo.type
        let reduced_type ← forallMetaTelescope ty
        let thmConclusionType := reduced_type.snd.snd
        let thmGoal ← mkFreshExprMVar thmConclusionType
        logInfo m!"theorem conclusion type: {thmConclusionType}"
        -- let filled := replaceWithEq (repl := thmConclusionType)
        liftMetaTactic (fun goal ↦ MVarId.apply goal thmConclusionType)

        -- -- goals from mvars
        -- let mut mVarGoals : List MVarId := []
        -- for mv in reduced_type.fst do
        --   let mVarGoal ← mkFreshExprMVar mv
        --   mVarGoals := mVarGoals ++ [mVarGoal.mvarId!]

        -- -- build `main goal = theorem conclusion`
        -- let eq ← mkEq origMainGoalType thmConclusionType
        -- let eqGoal ← mkFreshExprMVar eq
        -- logInfo m!"goalType = thmConclusion: {eq}"
        -- -- TODO: ideally one equality for each parameter of goal inductive predicate
        -- -- FIXME: change of goals is bad
        -- -- setGoals ([eqGoal.mvarId!] ++ [thmGoal.mvarId!] ++ mVarGoals ++ List.tail origGoals)

      | none => failure
      )

elab "replace_with_eq_apply" : tactic =>
  replaceWithEqApply

set_option trace.Elab.definition true

theorem almost_var_automatic :
    IndProp (.extend Γ A) (op (.incr .id) (op .id A)) :=
  by
    apply replaceWithEq
    case repl => replace_with_eq_apply; any_goals assumption
    · sorry
    · apply IndProp.var
