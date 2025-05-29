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
