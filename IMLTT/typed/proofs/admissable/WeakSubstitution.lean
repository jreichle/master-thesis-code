import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.RulesEquality
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

theorem weak_substitution_type :
    (Γ ⬝ S) ⊢ A type → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S) ⊢ A⌈s↑/ₙ(gen_ctx_leq .start)⌉ type :=
  by
    intro hA hsS
    have hS : Γ ⊢ S type := ctx_extr (boundary_ctx_type hA)
    have hWeak : Γ ⬝ S ⬝ S⌊↑ₚidₚ⌋ ⊢ A⌊⇑ₚ↑ₚidₚ⌋ type := weakening_second_type hA hS
    have hSub := substitution_type hWeak hsS
    apply_subst_eq hSub

theorem weak_substitution_term :
    ((Γ ⬝ S) ⊢ a ∶ A) → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S) ⊢ a⌈s↑/ₙ(gen_ctx_leq .start)⌉ ∶ A⌈s↑/ₙ(gen_ctx_leq .start)⌉ :=
  by
    intro haA hsS
    have hS := ctx_extr (boundary_ctx_term haA)
    have hWeak := weakening_second_term haA hS
    have hSub := substitution_term hWeak hsS
    apply_subst_eq hSub

theorem weak_substitution_general_ctx {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {S : Tm l} {s : Tm (l + 1)} :
    (Γ ⬝ S ⊗ Δ) ctx → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ctx :=
  by
    intro hiC hsS
    have hS : Γ ⊢ S type := ctx_extr (boundary_ctx_term hsS)
    rw [extend_start_expand_context] at hiC
    have hWeak := weakening_general_context hiC hS
    simp [extend_start_expand_context_weaken_from] at hWeak
    rw [weaken_from_zero] at hWeak
    have hSub := substitution_general_context hWeak hsS
    rw [←weak_substitution_eq_weakening_substitution_gen_context]
    apply hSub
    omega

theorem weak_substitution_general_type {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {A : Tm n} {S : Tm l} {s : Tm (l + 1)} :
    (Γ ⬝ S ⊗ Δ) ⊢ A type → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ A⌈s↑/ₙ(gen_ctx_leq Δ)⌉ type :=
  by
    intro hA hsS
    have hS : Γ ⊢ S type := ctx_extr (boundary_ctx_term hsS)
    rw [extend_start_expand_context] at hA
    have hWeak := weakening_general_type hA hS
    simp [extend_start_expand_context_weaken_from] at hWeak
    rw [weaken_from_zero] at hWeak
    have hSub := substitution_general_type hWeak hsS
    rw [←weak_substitution_eq_weakening_substitution_gen_context]
    rw [←weak_substitution_eq_weakening_substitution]
    apply hSub
    omega

theorem weak_substitution_general_term {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A a : Tm (n)} {S : Tm l} {s : Tm (l + 1)} :
    ((Γ ⬝ S ⊗ Δ) ⊢ a ∶ A) → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ a⌈s↑/ₙ(gen_ctx_leq Δ)⌉ ∶ A⌈s↑/ₙ(gen_ctx_leq Δ)⌉ :=
  by
    intro haA hsS
    have hS : Γ ⊢ S type := ctx_extr (boundary_ctx_term hsS)
    rw [extend_start_expand_context] at haA
    have hWeak := weakening_general_term haA hS
    simp [extend_start_expand_context_weaken_from] at hWeak
    rw [weaken_from_zero] at hWeak
    have hSub := substitution_general_term hWeak hsS
    rw [←weak_substitution_eq_weakening_substitution_gen_context]
    rw [←weak_substitution_eq_weakening_substitution]
    rw [←weak_substitution_eq_weakening_substitution]
    apply hSub
    omega

theorem weak_substitution_general_type_eq {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A A' : Tm (n)} {S : Tm l} {s : Tm (l + 1)} :
    (Γ ⬝ S ⊗ Δ) ⊢ A ≡ A' type → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ A⌈s↑/ₙ(gen_ctx_leq Δ)⌉ ≡ A'⌈s↑/ₙ(gen_ctx_leq Δ)⌉ type :=
  by
    intro hAA hsS
    have hS : Γ ⊢ S type := ctx_extr (boundary_ctx_term hsS)
    rw [extend_start_expand_context] at hAA
    have hWeak := weakening_general_type_eq hAA hS
    simp [extend_start_expand_context_weaken_from] at hWeak
    rw [weaken_from_zero] at hWeak
    have hSub := substitution_general_type_eq hWeak hsS
    rw [←weak_substitution_eq_weakening_substitution_gen_context]
    rw [←weak_substitution_eq_weakening_substitution]
    rw [←weak_substitution_eq_weakening_substitution]
    apply hSub
    omega

theorem weak_substitution_general_term_eq {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A a a' : Tm (n)} {S : Tm l} {s : Tm (l + 1)} :
    ((Γ ⬝ S ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1))) ⊢ a⌈s↑/ₙ(gen_ctx_leq Δ)⌉ ≡ a'⌈s↑/ₙ(gen_ctx_leq Δ)⌉
                                                ∶ A⌈s↑/ₙ(gen_ctx_leq Δ)⌉ :=
  by
    intro haaA hsS
    have hS : Γ ⊢ S type := ctx_extr (boundary_ctx_term hsS)
    rw [extend_start_expand_context] at haaA
    have hWeak := weakening_general_term_eq haaA hS
    simp [extend_start_expand_context_weaken_from] at hWeak
    rw [weaken_from_zero] at hWeak
    have hSub := substitution_general_term_eq hWeak hsS
    rw [←weak_substitution_eq_weakening_substitution_gen_context]
    rw [←weak_substitution_eq_weakening_substitution]
    rw [←weak_substitution_eq_weakening_substitution]
    rw [←weak_substitution_eq_weakening_substitution]
    apply hSub
    omega
