import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem boundary_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x}, Γ ⊢ A type → Γ ⊢ A type → Γ ⬝ A ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n Γ A hA _ihA
    apply weakening_type hA hA

theorem boundary_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A) → Γ ⊢ B type → Γ ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n x Γ A B hvA hB ihvA ihB
    apply weakening_type
    · apply ihvA
    · apply ihB

theorem boundary_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝟙 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.unit_form hiC

theorem boundary_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)}, (Γ ⬝ A ⊢ b ∶ B) → Γ ⬝ A ⊢ B type → Γ ⊢ ΠA;B type :=
  by
    intro n Γ A b B _hbB ihbB
    apply IsType.pi_form
    · have hiCA := boundary_ctx_type ihbB
      apply ctx_extr hiCA
    · apply ihbB

theorem boundary_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A) → (Γ ⊢ b ∶ B⌈a⌉₀) → Γ ⬝ A ⊢ B type → Γ ⊢ A type → Γ ⊢ B⌈a⌉₀ type → Γ ⬝ A ⊢ B type → Γ ⊢ ΣA;B type :=
  by
    intro n Γ a A b B haA hbB hB ihaA ihbB ihB
    apply IsType.sigma_form
    · apply ihaA
    · apply hB

theorem boundary_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, Γ ⊢ A type → (Γ ⊢ a ∶ A) → Γ ⊢ A type → Γ ⊢ A type → Γ ⊢ a ≃[A] a type :=
  by
    intro n Γ A a hA haA ihA ihaA
    apply IsType.iden_form
    · apply hA
    · apply haA
    · apply haA

theorem boundary_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.univ_form hiC

theorem boundary_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC hiC
    apply IsType.univ_form hiC

theorem boundary_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) → (Γ ⬝ A ⊢ B ∶ 𝒰) → Γ ⊢ 𝒰 type → Γ ⬝ A ⊢ 𝒰 type → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A B hAU hBU ihAU ihBU
    apply ihAU

theorem boundary_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) → (Γ ⬝ A ⊢ B ∶ 𝒰) → Γ ⊢ 𝒰 type → Γ ⬝ A ⊢ 𝒰 type → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A B hAU hBU ihAU ihBU
    apply ihAU

theorem boundary_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰) → (Γ ⊢ a ∶ A) → (Γ ⊢ a' ∶ A) → Γ ⊢ 𝒰 type → Γ ⊢ A type → Γ ⊢ A type → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA'
    apply ihAU

theorem boundary_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type → (Γ ⊢ a ∶ A⌈⋆⌉₀) → (Γ ⊢ b ∶ 𝟙) → Γ ⬝ 𝟙 ⊢ A type → Γ ⊢ A⌈⋆⌉₀ type → Γ ⊢ 𝟙 type → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A a b hA haA hb1 ihA ihaA ihb1
    apply substitution_type
    · apply hb1
    · apply hA

theorem boundary_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type → (Γ ⊢ b ∶ 𝟘) → Γ ⬝ 𝟘 ⊢ A type → Γ ⊢ 𝟘 type → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A b hA hb0 ihA ihb0
    apply substitution_type
    · apply hb0
    · apply hA

theorem boundary_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B) → (Γ ⊢ a ∶ A) → Γ ⊢ ΠA;B type → Γ ⊢ A type → Γ ⊢ B⌈a⌉₀ type :=
  by
    intro n Γ f A B a hfPi haA ihfPi ihaA
    apply substitution_type
    · apply haA
    · apply And.right (pi_is_type_inversion ihfPi)

theorem boundary_sigma_first :
    ∀ {n : Nat} {Γ : Ctx n} {p A : Tm n} {B : Tm (n + 1)}, (Γ ⊢ p ∶ ΣA;B) → Γ ⊢ ΣA;B type → Γ ⊢ A type :=
  by
    intro n Γ p A B hpSi ihpSi
    have h := sigma_is_type_inversion ihpSi
    apply And.left h

theorem boundary_sigma_second :
    ∀ {n : Nat} {Γ : Ctx n} {p A : Tm n} {B : Tm (n + 1)}, (Γ ⊢ p ∶ ΣA;B) → Γ ⊢ ΣA;B type → Γ ⊢ B⌈π₁ p⌉₀ type :=
  by
    intro n Γ p A B hpSi ihpSi
    have h := sigma_is_type_inversion ihpSi
    apply substitution_type
    · apply HasType.sigma_first hpSi
    · apply And.right h

theorem boundary_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a a' p : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (Γ ⊢ p ∶ a ≃[A] a') →
            Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
              Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type →
                (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
                  Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
                    Γ ⊢ A type →
                      Γ ⊢ A type →
                        Γ ⊢ a ≃[A] a' type →
                          Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
                            Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type → Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type :=
  by
    intro n Γ A B b a a' p hB hbB haA haA' hpId hBa hBc ihB ihbB ihaA ihaA' ihpId ihBa ihBc
    apply ihBc

theorem boundary_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ A ≡ B type → Γ ⊢ A type → Γ ⊢ A type ∧ Γ ⊢ B type → Γ ⊢ B type :=
  by
    intro n Γ a A B haA hAB ihaA ihAB
    apply And.right ihAB
