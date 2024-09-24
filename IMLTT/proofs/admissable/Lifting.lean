import IMLTT.AbstractSyntax
import IMLTT.Substitution
import IMLTT.JudgmentsAndRules

theorem lifting_ctx_one_term : Γ ⬝ (lift i j A) = Γ, (lift_ctx i j (Ctx.empty ⬝ A)) :=
  sorry
