import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

theorem shift_weaken_from {hl : l ≤ n} :
    A⌊↑ₚidₚ⌋⌊weaken_from (n + 1) l⌋ = A⌊weaken_from n l⌋⌊↑ₚidₚ⌋ :=
  by
    substitution_step

theorem weak_subst_sigma_C {leq : l ≤ n}:
    C⌊weaken_from (n + 1) l⌋⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ =
    C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌊weaken_from (n + 1 + 1) l⌋ :=
  by
    substitution_step
    substitution_step

theorem weak_subst_sigma_c :
    c⌈(ₛidₚ), a, b⌉⌊ρ⌋
    = c⌊lift_weak_n 2 ρ⌋⌈(ₛidₚ), (a⌊ρ⌋), (b⌊ρ⌋)⌉ :=
  by
    substitution_step
    aesop

theorem helper_weakening_iden_elim_B :
    B⌈(ₛidₚ), a, b, c⌉⌊ρ⌋
    = B⌊lift_weak_n 3 ρ⌋⌈(ₛidₚ), (a⌊ρ⌋), (b⌊ρ⌋), (c⌊ρ⌋)⌉ :=
  by
    substitution_step
    aesop

theorem helper_weak_iden_propagate_weak {leq : l ≤ n} :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌊weaken_from (n + 1 + 1) l⌋
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋⌊weaken_from (n + 1 + 1) l⌋] v(0) :=
  by
    substitution_step
    substitution_step

theorem helper_weakening_iden_elim_B_refl {leq : l ≤ n} :
    B⌊⇑ₚ⇑ₚ↑₁n + 1↬l⌋⌈(ₛidₚ), v(0), (A⌊↑₁n↬l⌋⌊↑ₚidₚ⌋.refl v(0))⌉
    = B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉⌊↑₁n + 1↬l⌋ :=
  by
    substitution_step
    substitution_step

theorem tleq {l : Nat} :
    l + 1 ≤ 0 -> False :=
  by
    intro hLeq
    omega

theorem helper_weak_1 :
    l ≤ x → x + 1 ≤ l → False :=
  by
    intro h1 h2
    omega

theorem helper_weak_nat_succ {leq : l ≤ n} :
    A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌊weaken_from (n + 1 + 1) l⌋
    = A⌊1ₙ⇑ₚweaken_from n l⌋⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ :=
  by
    substitution_step
    substitution_step
