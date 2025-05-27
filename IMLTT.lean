import IMLTT.typed.proofs.boundary.BoundaryTypesTerms
import IMLTT.typed.SigmaProjections
import IMLTT.typed.PropositionalEquality

inductive All {α : Type u} (P : α → Prop) : List α → Prop where
  | nil  : All P []
  | cons : ∀ {x xs}, P x → All P xs → All P (x :: xs)

set_option pp.proofs true
#check All.rec

theorem All_map {α β : Type u} {P : α → Prop} {Q : β → Prop} {f : α → β} {h : ∀ x, P x → Q (f x)} :
  ∀xs, All P xs → All Q (xs.map f) :=
  by
    intro xs
    apply All.rec
    case nil =>
      simp [List.map]
      apply All.nil
    case cons =>
      intro x xs hPx hPxs ihPx
      simp [List.map]
      exact All.cons (h x hPx) ihPx

theorem All_map' {α β : Type u} {P : α → Prop} {Q : β → Prop} {f : α → β} {h : ∀ x, P x → Q (f x)} :
    ∀xs, All P xs → All Q (xs.map f) :=
  fun _xs ↦ All.rec
    (motive := fun xs _hPxs ↦ All Q (xs.map f))
    (All.nil)
    (fun {x} {_xs} hPx _hpXs ihPxs ↦ (All.cons (h x hPx) ihPxs))

theorem test :
    A⌈𝓈(x)⌉₀⌊↑ₚidₚ⌋ = A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋⌈⇑ₛ((ₛidₚ)⋄ x)⌉ := -- s⌈⇑ₛ((ₛidₚ)⋄ x)⌉ ∶ A⌈𝓈(x)⌉₀⌊↑ₚidₚ⌋
  by
    simp []
    substitution_norm

-- theorem boundary_iden_elim' :
--   ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
--   (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
--   → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
--   → (Γ ⊢ a ∶ A)
--   → (Γ ⊢ a' ∶ A)
--   → (Γ ⊢ p ∶ a ≃[A] a')
--   → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))) ⊢ B type
--   → Γ ⬝ A ⊢ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ type
--   → Γ ⊢ A type
--   → Γ ⊢ A type
--   → Γ ⊢ a ≃[A] a' type
--   → Γ ⊢ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ type :=
--   by
--     intro n Γ A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId
--     apply_subst_eq substitution_type
--     case b => apply p
--     case A => apply B⌈⇑ₛ((ₛidₚ)⋄ a⋄ a')⌉
--     · substitution_norm
--     rotate_left
--     · apply hpId
--     · apply_subst_eq substitution_type
--       case b => apply a'⌊↑ₚidₚ⌋
--       case A => apply B⌈⇑ₛ⇑ₛ((ₛidₚ)⋄ a)⌉
--       · substitution_norm
--       rotate_left
--       · sorry
--       · sorry
