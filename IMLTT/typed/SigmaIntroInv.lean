import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.WeakSubstitution.WeakSubstitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConv

import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

theorem sigma_inversion_left_one
    (a_1 : Nat                    )
    (Γ : Ctx a_1                  )
    (a b A : Tm a_1               )
    (B : Tm (a_1 + 1)             )
    (hpSi : Γ ⊢ a&b ∶ ΣA;B        )
    (x : Nat                      )
    (Γ_1 : Ctx x                  )
    (i : Fin x                    )
    (A_1 B_1 : Tm x               )
    (a_2 : Γ_1 ⊢ v(i) ∶ A_1       )
    (a_ih_1 : Γ_1 ⊢ B_1 type      )
    (a_4 b_1 A_2 : Tm (x + 1)     )
    (B_2 : Tm (x + 1 + 1)         )
    (left : v(i)⌊↑ₚidₚ⌋ = a_4&b_1 )
    (right : A_1⌊↑ₚidₚ⌋ = ΣA_2;B_2)
    : Γ_1 ⬝ B_1 ⊢ a_4 ∶ A_2 :=
  by
    cases left

theorem sigma_inversion_left_right
    (a_1 : Nat                    )
    (Γ : Ctx a_1                  )
    (a b A : Tm a_1               )
    (B : Tm (a_1 + 1)             )
    (hpSi : Γ ⊢ a&b ∶ ΣA;B        )
    (x : Nat                      )
    (Γ_1 : Ctx x                  )
    (i : Fin x                    )
    (A_1 B_1 : Tm x               )
    (a_2 : Γ_1 ⊢ v(i) ∶ A_1       )
    (a_ih_1 : Γ_1 ⊢ B_1 type      )
    (a_4 b_1 A_2 : Tm (x + 1)     )
    (B_2 : Tm (x + 1 + 1)         )
    (left : v(i)⌊↑ₚidₚ⌋ = a_4&b_1 )
    (right : A_1⌊↑ₚidₚ⌋ = ΣA_2;B_2)
    : Γ_1 ⬝ B_1 ⊢ b_1 ∶ B_2⌈a_4⌉₀ :=
  by
    cases left

theorem sigma_inversion_left_two
    (a_1 : Nat                                 ) 
    (Γ : Ctx a_1                               )
    (a b A : Tm a_1                            )
    (B : Tm (a_1 + 1)                          )
    (hpSi : Γ ⊢ a&b ∶ ΣA;B                     )
    (n : Nat                                   )
    (Γ_1 : Ctx n                               )
    (A_1 a_5 b_1 A_2 : Tm n                    )
    (B_2 : Tm (n + 1)                          )
    (a_3 : Γ_1 ⊢ a_5&b_1 ∶ A_1                 )
    (a_4 : Γ_1 ⊢ A_1 ≡ ΣA_2;B_2 type           )
    (a_ih : ∀ (a b A : Tm n) (B : Tm (n + 1)),
            a_5 = a → b_1 = b → (A_1 = ΣA;B)   
            → (Γ_1 ⊢ a ∶ A) ∧ Γ_1 ⊢ b ∶ B⌈a⌉₀  )
    : Γ_1 ⊢ a_5 ∶ A_2 :=
  by
    sorry

theorem sigma_inversion_right_two
    (a_1 : Nat                                )
    (Γ : Ctx a_1                              )
    (a b A : Tm a_1                           )
    (B : Tm (a_1 + 1)                         )
    (hpSi : Γ ⊢ a&b ∶ ΣA;B                    )
    (n : Nat                                  )
    (Γ_1 : Ctx n                              )
    (A_1 a_5 b_1 A_2 : Tm n                   )
    (B_2 : Tm (n + 1)                         )
    (a_3 : Γ_1 ⊢ a_5&b_1 ∶ A_1                )
    (a_4 : Γ_1 ⊢ A_1 ≡ ΣA_2;B_2 type          )
    (a_ih : ∀ (a b A : Tm n) (B : Tm (n + 1)), 
            a_5 = a → b_1 = b → (A_1 = ΣA;B) 
            → (Γ_1 ⊢ a ∶ A) ∧ Γ_1 ⊢ b ∶ B⌈a⌉₀ )
    : Γ_1 ⊢ b_1 ∶ B_2⌈a_5⌉₀ :=
  by
    sorry

theorem sigma_intro_inversion :
    (Γ ⊢ a&b ∶ ΣA;B) → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ b ∶ B⌈a⌉₀) :=
  by
    intro hpSi
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ x X _haA =>
         ∀ a b A B,
         x = (a&b) ∧ X = (ΣA;B) → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ b ∶ B⌈a⌉₀))
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      hpSi
    case ty_conv =>
      intro n Γ' x X Y hxX hXY ihxX _ihxY a' b' A' B' heq
      cases (And.left heq)
      cases (And.right heq)
      sorry
    any_goals sorry
