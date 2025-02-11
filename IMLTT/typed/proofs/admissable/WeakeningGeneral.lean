import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx


theorem shift_weaken_from {hl : l ≤ n} :
    A⌊↑ₚidₚ⌋⌊weaken_from (n + 1) l⌋ = A⌊weaken_from n l⌋⌊↑ₚidₚ⌋ :=
  by
    simp [weaken_from]
    split
    case isTrue hT =>
      simp [weakening_comp]
      simp [comp_weaken]
      rw [←weakening_shift_id]
      rw [←weakening_comp]
      rw [weakening_id]
      rw [weakening_shift_id]
    case isFalse hF =>
      omega

theorem weak_subst_sigma_C {leq : l ≤ n}:
    C⌊weaken_from (n + 1) l⌋⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ =
    C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌊weaken_from (n + 1 + 1) l⌋ :=
  by
    simp [substitution_comp_ρσ]
    simp [substitution_comp_σρ]
    rw [←lift_weaken_from]
    · apply substitution_var_substitute
      intro x
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          rw [←lift_weaken_from]
          · rw [←lift_weaken_from]
            · simp [comp_weaken_substitute]
              simp [comp_substitute_weaken]
              simp [substitute]
              simp [substitute_var]
              simp [weaken]
              simp [weaken_var]
              aesop
            · omega
          · omega
        | succ i' =>
          rw [←lift_weaken_from]
          · rw [←lift_weaken_from]
            · simp [comp_weaken_substitute]
              simp [comp_substitute_weaken]
              simp [substitute]
              simp [substitute_var]
              simp [←substitution_conv_var]
              rw [←substitution_comp_σρ]
              simp [comp_weaken]
              rw [←weakening_shift_id]
              rw (config := {occs := .pos [2]}) [←weakening_shift_id]
              rw [←weakening_comp]
              rw [weakening_id]
              rw (config := {occs := .pos [1]}) [weakening_shift_id]
              rfl
            · omega
          · omega
    · exact leq

theorem weak_subst_sigma_c :
    c⌈(ₛidₚ), a, b⌉⌊ρ⌋
    = c⌊lift_weak_n 2 ρ⌋⌈(ₛidₚ), (a⌊ρ⌋), (b⌊ρ⌋)⌉ :=
  by
    rw [substitution_comp_ρσ]
    rw [substitution_comp_σρ]
    apply substitution_var_substitute
    intro x
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [←substitution_comp_σρ]
      simp [weaken]
      simp [weakening_var_lift_n_id]
      simp [←weakening_conv_var]
      simp [weakening_id]
    | shift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]
      apply substitution_var_substitute
      intro x
      rw [←substitution_conv_shift_id]
      cases x with
      | mk i hFin =>
        induction i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          rw [←weakening_shift_id]
          rw (config := {occs := .pos [2]}) [←weakening_shift_id]
          simp [weakening_id]
          rfl
        | succ i' hInd =>
          simp [substitute]
          simp [substitute_var]
          cases i' with
          | zero =>
            simp [←substitution_conv_var]
            rw [←substitution_comp_ρσ]
            simp [substitute]
            simp [substitute_var]
            simp [weakening_shift_id]
            rfl
          | succ j =>
            simp [substitute_var]
            cases j with
            | zero =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
            | succ j' =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
    | lift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]

theorem weak_subst_iden_elim :
    B⌈(ₛidₚ), a, b, c⌉⌊ρ⌋
    = B⌊lift_weak_n 3 ρ⌋⌈(ₛidₚ), (a⌊ρ⌋), (b⌊ρ⌋), (c⌊ρ⌋)⌉ :=
  by
    rw [substitution_comp_ρσ]
    rw [substitution_comp_σρ]
    apply substitution_var_substitute
    intro x
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
      simp [←substitution_comp_σρ]
      simp [weaken]
      simp [weakening_var_lift_n_id]
      simp [←weakening_conv_var]
      simp [weakening_id]
    | shift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]
      apply substitution_var_substitute
      intro x
      rw [←substitution_conv_shift_id]
      cases x with
      | mk i hFin =>
        induction i with
        | zero =>
          simp [substitute]
          simp [substitute_var]
          rw [←weakening_shift_id]
          rw (config := {occs := .pos [2]}) [←weakening_shift_id]
          simp [weakening_id]
          rfl
        | succ i' hInd =>
          simp [substitute]
          simp [substitute_var]
          cases i' with
          | zero =>
            simp [←substitution_conv_var]
            rw [←substitution_comp_ρσ]
            simp [substitute]
            simp [substitute_var]
            simp [weakening_shift_id]
            rfl
          | succ j =>
            simp [substitute_var]
            cases j with
            | zero =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
            | succ j' =>
              simp [←substitution_conv_var]
              rw [←substitution_comp_ρσ]
              simp [substitute]
              simp [substitute_var]
              simp [weakening_shift_id]
              rfl
    | lift ρ' =>
      simp [comp_weaken_substitute]
      simp [comp_substitute_weaken]
      simp [comp_weaken]

theorem helper_weak_iden_propagate_weak {leq : l ≤ n} :
    (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌊weaken_from (n + 1 + 1) l⌋
    = v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋⌊weaken_from (n + 1 + 1) l⌋] v(0) :=
  by
    rw [←lift_weaken_from]
    · rw [←lift_weaken_from]
      · simp [weaken]
        simp [weaken_var]
        apply And.intro
        · rfl
        · rfl
      · omega
    · omega

theorem helper_weak_refl_propagate_weak :
    .refl (A⌊weaken_from n l⌋) (a⌊weaken_from n l⌋)
    = (.refl A a)⌊weaken_from n l⌋ :=
  by
    · simp [weaken]

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

theorem weakening :
    (∀ {n : Nat} {Γ : Ctx n} (isCtx : Γ ctx)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n} (isType : Γ ⊢ A type)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ⊢ A⌊weaken_from n l⌋ type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n} (hasType : Γ ⊢ a ∶ A)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
        → insert_into_ctx (leq := leq) Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} (isEqualType : Γ ⊢ A ≡ A' type)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n} (isEqualTerm : Γ ⊢ a ≡ a' ∶ A)
      (l : Nat) {leq : l ≤ n} {B : Tm l},
      get_sub_context (leq := leq) Γ l ⊢ B type
      → insert_into_ctx (leq := leq) Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋)
    :=
  by
    apply judgment_recursor
      (motive_1 := fun {n} Γ _hiC =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ctx)
      (motive_2 := fun {n} Γ A _hA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ A⌊weaken_from n l⌋ type)
      (motive_3 := fun {n} Γ a A haA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋)
      (motive_4 := fun {n} Γ A A' _hAA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type)
      (motive_5 := fun {n} Γ a a' A _haaA =>
        ∀ l {leq : l ≤ n} {B : Tm l}, (get_sub_context Γ l leq) ⊢ B type
        → (insert_into_ctx leq Γ B) ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋)
    case IsCtxEmpty =>
      intro l hleq B hB
      simp [empty_insert_into_context]
      simp [insert_into_ctx]
      have hiCB := IsCtx.extend (boundary_ctx_type hB) hB
      have heq : l = 0 := by omega
      have B' : Tm 0 := heq ▸ B
      aesop
    case IsCtxExtend =>
      intro n Γ A hiC hA ihiC ihA l hLeq B hB
      cases hLeq
      case refl =>
        simp [insert_into_ctx]
        rw [head_get_sub_context] at hB
        apply IsCtx.extend
        · apply boundary_ctx_type hB
          apply rfl
        · apply hB
      case step h =>
        rw [extend_get_sub_context (leq := h)] at hB
        · rw [←extend_insert_into_context]
          apply IsCtx.extend
          · apply ihiC
            apply hB
          · apply ihA
            apply hB
    case IsTypeUnitForm =>
      intro n Γ hiC ihiC l hleq B hB
      simp [weaken]
      apply IsType.unit_form
      apply ihiC
      apply hB
    case IsTypeEmptyForm =>
      intro n Γ hiC ihiC l hleq B hB
      simp [weaken]
      apply IsType.empty_form
      apply ihiC
      apply hB
    case IsTypePiForm =>
      intro n Γ A B hA hB ihA ihB l hleq S hS
      simp [weaken]
      simp [lift_weak_n]
      apply IsType.pi_form
      · apply ihA
        · apply hS
      · rw [extend_insert_into_context]
        rw [lift_weaken_from]
        apply ihB
        simp [get_sub_context]
        split
        · exact hS
        · omega
        omega
    case IsTypeSigmaForm =>
      intro n Γ A B hA hB ihA ihB l hleq S hS
      simp [weaken]
      simp [lift_weak_n]
      apply IsType.sigma_form
      · apply ihA
        · apply hS
      · rw [extend_insert_into_context]
        rw [lift_weaken_from]
        apply ihB
        simp [get_sub_context]
        split
        · exact hS
        · omega
        omega
    case IsTypeIdenForm =>
      intro n Γ a A a' haA haA' ihaA ihaA' l hleq B hB
      simp [weaken]
      apply IsType.iden_form
      · apply ihaA
        apply hB
      · apply ihaA'
        apply hB
    case IsTypeUnivForm =>
      intro n Γ hiC ihiC l hleq B hB
      simp [weaken]
      apply IsType.univ_form
      apply ihiC
      apply hB
    case IsTypeUnivElim =>
      intro n Γ A hAU ihAU l hleq B hB
      apply IsType.univ_elim
      simp [weaken] at ihAU
      apply ihAU
      apply hB
    case HasTypeVar =>
      intro x Γ A hA ihA l hleq B hB
      cases hleq
      case refl =>
        simp [weaken_from]
        simp [weakening_comp]
        simp [comp_weaken]
        simp [insert_into_ctx]
        rw [←weakening_shift_id]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        simp [weakening_id]
        apply HasType.weak
        · apply HasType.var hA
        · rw [head_get_sub_context] at hB
          · apply hB
          · rfl
      case step h =>
        rw [←extend_insert_into_context (leq := h)]
        · simp [weakening_comp]
          simp [weaken_from]
          split
          case isTrue hT =>
            simp [comp_weaken]
            rw [←weakening_shift_id]
            simp [←weakening_comp]
            simp [weakening_id]
            simp [weaken]
            simp [weaken_var]
            apply HasType.var
            apply ihA
            rw [extend_get_sub_context] at hB
            apply hB
          case isFalse hF =>
            apply False.elim
            simp [h] at hF
            apply helper_weak_1 h hF
    case HasTypeWeak =>
      intro n x Γ A B hvA hB ihvA ihB l hleq S hS
      · cases hleq
        case refl =>
          simp [insert_into_ctx]
          simp [weaken_from]
          apply HasType.weak
          · rw [←weakening_conv_var]
            rw [head_get_sub_context (eq := by rfl)] at hS
            rw [head_insert_into_context]
            · cases n with
              | zero =>
                simp [weaken_from]
                rw [←head_insert_into_context]
                apply HasType.weak
                · apply hvA
                · apply hB
              | succ n' =>
                rw [←head_insert_into_context]
                apply HasType.weak
                · apply hvA
                · apply hB
          · rw [head_get_sub_context] at hS
            · apply hS
            · rfl
        case step h =>
          rw [shift_weaken_from]
          · rw [shift_weaken_from]
            · rw [←extend_insert_into_context]
              apply HasType.weak
              · simp [←weakening_conv_var]
                apply ihvA
                rw [extend_get_sub_context] at hS
                · apply hS
              · apply ihB
                rw [extend_get_sub_context] at hS
                apply hS
              · exact h
            · exact h
          · exact h
    case HasTypeUnitIntro =>
      intro n Γ hiC ihiC l hleq B hB
      simp [weaken]
      apply HasType.unit_intro
      apply ihiC
      apply hB
    case HasTypePiIntro =>
      intro n Γ A b B hbB ihbB l hleq S hS
      apply HasType.pi_intro
      rw [extend_insert_into_context]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      apply ihbB
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega
    case HasTypeSigmaIntro =>
      intro n Γ a A b B haA hbB ihaA ihbB l hleq S hS
      apply HasType.sigma_intro
      · apply ihaA
        apply hS
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · simp [weaken_from]
          split
          case a.isTrue h =>
            rw [←weak_sub_zero]
            apply ihbB
            apply hS
          case a.isFalse h =>
            omega
        · exact hleq
    case HasTypeIdenIntro =>
      intro n Γ A a haA ihaA l hleq B hB
      apply HasType.iden_intro
      apply ihaA
      apply hB
    case HasTypeUnivUnit =>
      intro n Γ hiC ihiC l hleq B hB
      simp [weaken]
      apply HasType.univ_unit
      apply ihiC
      apply hB
    case HasTypeUnivEmpty =>
      intro n Γ hiC ihiC l hleq B hB
      simp [weaken]
      apply HasType.univ_empty
      apply ihiC
      apply hB
    case HasTypeUnivPi =>
      intro n Γ A B hAU hBU ihAU ihBU l hleq S hS
      simp [weaken] at *
      simp [lift_weak_n]
      apply HasType.univ_pi
      · apply ihAU
        · apply hS
      · rw [extend_insert_into_context]
        rw [lift_weaken_from]
        apply ihBU
        simp [get_sub_context]
        split
        · exact hS
        · omega
        omega
    case HasTypeUnivSigma =>
      intro n Γ A B hAU hBU ihAU ihBU l hleq S hS
      simp [weaken] at *
      simp [lift_weak_n]
      apply HasType.univ_sigma
      · apply ihAU
        · apply hS
      · rw [extend_insert_into_context]
        rw [lift_weaken_from]
        apply ihBU
        simp [get_sub_context]
        split
        · exact hS
        · omega
        omega
    case HasTypeUnivIden =>
      intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA' l hleq B hB
      simp [weaken]
      apply HasType.univ_iden
      · apply ihAU
        · apply hB
      · apply ihaA
        · apply hB
      · apply ihaA'
        · apply hB
    case HasTypeUnitElim =>
      intro n Γ A a b hA haA hb1 ihA ihaA ihb1 l hleq B hB
      rw [weak_sub_zero]
      apply HasType.unit_elim
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [←weakening_unit]
        rw [extend_insert_into_context]
        apply ihA
        · rw [extend_get_sub_context]
          exact hB
        · exact hleq
      · simp [lift_weak_n]
        simp [lift_single_subst_tt]
        apply ihaA
        apply hB
      · apply ihb1
        apply hB
    case HasTypeEmptyElim =>
      intro n Γ A b hA hb0 ihA ihb0 l hleq S hS
      rw [weak_sub_zero]
      apply HasType.empty_elim
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [←weakening_empty]
        rw [extend_insert_into_context]
        apply ihA
        · rw [extend_get_sub_context]
          exact hS
        · exact hleq
      · apply ihb0
        apply hS
    case HasTypePiElim =>
      intro n Γ f A B a hfPi haA ihfPi ihaA l hleq S hS
      rw [weak_sub_zero]
      · apply HasType.pi_elim
        · apply ihfPi
          apply hS
        · apply ihaA
          apply hS
    case HasTypeSigmaElim =>
      intro n Γ A B p C c hpSi hC hcC ihpSi ihC ihcC l hleq S hS
      rw [weak_sub_zero]
      apply HasType.sigma_elim
      · apply ihpSi
        apply hS
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · rw (config := {occs := .pos [1]}) [←lift_weaken_from]
          · rw [←weakening_sigma]
            rw [extend_insert_into_context]
            apply ihC
            rw [extend_get_sub_context]
            apply hS
          · exact hleq
        · exact hleq
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · rw [lift_weaken_from]
          · rw [weak_subst_sigma_C]
            · simp [extend_insert_into_context]
              apply ihcC
              rw [extend_get_sub_context]
              rw [extend_get_sub_context]
              apply hS
            · exact hleq
          · omega
        · omega
    case HasTypeIdenElim =>
      intro n Γ A B b a a' p hB hbB hpId hB' ihB ihbB ihpId ihB' l hleq S hS
      rw [weak_subst_iden_elim]
      apply HasType.iden_elim
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [lift_weaken_from]
        rw [lift_weaken_from]
        rw [extend_insert_into_context]
        rw [←shift_weaken_from]
        rw [extend_insert_into_context]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        rw [←shift_weaken_from]
        rw [←shift_weaken_from]
        rw [weakening_shift_id]
        rw [←helper_weak_iden_propagate_weak]
        rw [extend_insert_into_context]
        apply ihB
        rw [extend_get_sub_context]
        rw [extend_get_sub_context]
        rw [extend_get_sub_context]
        apply hS
        any_goals omega
      · rw [helper_weak_refl_propagate_weak]
        rw [←weak_subst_iden_elim]
        apply ihbB
        apply hS
      · apply ihpId
        apply hS
      · rw [←weak_subst_iden_elim]
        apply ihB'
        apply hS
    case HasTypeTyConv =>
      intro n Γ a A B haA hAB ihaA ihAB l hleq S hS
      apply HasType.ty_conv
      · apply ihaA
        apply hS
      · apply ihAB
        apply hS
    case HasTypeTyConvSymm =>
      intro n Γ a A B haA hAB ihaA ihAB l hleq S hS
      apply HasType.ty_conv_symm
      · apply ihaA
        apply hS
      · apply ihAB
        apply hS
    case IsEqualTypeUnitFormEq =>
      intro n Γ hiC ihiC l hleq S hS
      apply IsEqualType.unit_form_eq
      apply ihiC
      apply hS
    case IsEqualTypeEmptyFormEq =>
      intro n Γ hiC ihiC l hleq S hS
      apply IsEqualType.empty_form_eq
      apply ihiC
      apply hS
    case IsEqualTypePiFormEq =>
      intro n Γ A A' B B' hAA hBB ihAA ihBB l hleq S hS
      apply IsEqualType.pi_form_eq
      · apply ihAA
        apply hS
      · rw [extend_insert_into_context]
        simp [lift_weak_n]
        rw [lift_weaken_from]
        · apply ihBB
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
    case IsEqualTypeSigmaFormEq =>
      intro n Γ A A' B B' hAA hBB ihAA ihBB l hleq S hS
      apply IsEqualType.sigma_form_eq
      · apply ihAA
        apply hS
      · rw [extend_insert_into_context]
        simp [lift_weak_n]
        rw [lift_weaken_from]
        · apply ihBB
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
    case IsEqualTypeIdenFormEq =>
      intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA' l hleq S hS
      apply IsEqualType.iden_form_eq
      · apply ihAA
        apply hS
      · apply ihaaA
        apply hS
      · apply ihaaA'
        apply hS
    case IsEqualTypeUnivFormEq =>
      intro n Γ hiC ihiC l hleq S hS
      apply IsEqualType.univ_form_eq
      apply ihiC
      apply hS
    case IsEqualTypeUnivElimEq =>
      intro n Γ A A' hAAU ihAAU l hleq S hS
      apply IsEqualType.univ_elim_eq
      apply ihAAU
      apply hS
    case IsEqualTypeTypeSymm =>
      intro n Γ A A' hAA ihAA l hleq S hS
      apply IsEqualType.type_symm
      apply ihAA
      apply hS
    case IsEqualTypeTypeTrans =>
      intro n Γ A B C hAB hBC ihAB ihBC l hleq S hS
      apply IsEqualType.type_trans
      · apply ihAB
        apply hS
      · apply ihBC
        apply hS
    case IsEqualTermVarEq =>
      intro n Γ A hA ihA l hleq S hS
      cases hleq
      case refl =>
        simp [weaken_from]
        simp [weakening_comp]
        simp [comp_weaken]
        simp [insert_into_ctx]
        rw [←weakening_shift_id]
        rw (config := {occs := .pos [3]}) [←weakening_shift_id]
        simp [weakening_id]
        apply IsEqualTerm.weak_eq
        · apply IsEqualTerm.var_eq hA
        · rw [head_get_sub_context] at hS
          · apply hS
          · rfl
      case step h =>
        rw [←extend_insert_into_context (leq := h)]
        · simp [weakening_comp]
          simp [weaken_from]
          split
          case isTrue hT =>
            simp [comp_weaken]
            rw [←weakening_shift_id]
            simp [←weakening_comp]
            simp [weakening_id]
            simp [weaken]
            simp [weaken_var]
            apply IsEqualTerm.var_eq
            apply ihA
            rw [extend_get_sub_context] at hS
            apply hS
          case isFalse hF =>
            apply False.elim
            simp [h] at hF
            apply helper_weak_1 h hF
    case IsEqualTermWeakEq =>
      intro n x Γ A B hvA hB ihvA ihB l hleq S hS
      · cases hleq
        case refl =>
          simp [insert_into_ctx]
          simp [weaken_from]
          apply IsEqualTerm.weak_eq
          · rw [←weakening_conv_var]
            rw [head_get_sub_context (eq := by rfl)] at hS
            rw [head_insert_into_context]
            · cases n with
              | zero =>
                simp [weaken_from]
                rw [←head_insert_into_context]
                apply IsEqualTerm.weak_eq
                · apply hvA
                · apply hB
              | succ n' =>
                rw [←head_insert_into_context]
                apply IsEqualTerm.weak_eq
                · apply hvA
                · apply hB
          · rw [head_get_sub_context] at hS
            · apply hS
            · rfl
        case step h =>
          rw [shift_weaken_from]
          · rw [shift_weaken_from]
            · rw [←extend_insert_into_context]
              apply IsEqualTerm.weak_eq
              · simp [←weakening_conv_var]
                apply ihvA
                rw [extend_get_sub_context] at hS
                apply hS
              · apply ihB
                rw [extend_get_sub_context] at hS
                apply hS
              · apply h
            · exact h
          · exact h
    case IsEqualTermUnitComp =>
      intro n Γ A a hA haA ihA ihaA l hleq S hS
      rw [weak_sub_zero]
      apply IsEqualTerm.unit_comp
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [←weakening_unit]
        rw [extend_insert_into_context]
        · apply ihA
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
      · simp [lift_weak_n]
        simp [lift_single_subst_tt]
        apply ihaA
        apply hS
    case IsEqualTermPiComp =>
      intro n Γ A b B a hbB haA ihbB ihaA l hleq S hS
      rw [weak_sub_zero]
      rw [weak_sub_zero]
      apply IsEqualTerm.pi_comp
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [extend_insert_into_context]
        · apply ihbB
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
      · apply ihaA
        apply hS
    case IsEqualTermSigmaComp =>
      intro n Γ a A b B C c haA hbB hC hcC ihaA ihbB ihC ihcC l hleq S hS
      rw [weak_sub_zero]
      rw [weak_subst_sigma_c]
      apply IsEqualTerm.sigma_comp
      · apply ihaA
        apply hS
      · simp [lift_weak_n]
        rw [←weak_sub_zero]
        apply ihbB
        apply hS
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · rw (config := {occs := .pos [1]}) [←lift_weaken_from]
          · rw [←weakening_sigma]
            rw [extend_insert_into_context]
            apply ihC
            rw [extend_get_sub_context]
            apply hS
          · exact hleq
        · exact hleq
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · rw [lift_weaken_from]
          · rw [weak_subst_sigma_C]
            · simp [extend_insert_into_context]
              apply ihcC
              rw [extend_get_sub_context]
              · rw [extend_get_sub_context]
                apply hS
            · exact hleq
          · omega
        · omega
    case IsEqualTermIdenComp =>
      intro n Γ A B b a hB hbB haA hB' ihB ihbB ihaA ihB' l hleq s hS
      rw [weak_subst_iden_elim]
      apply IsEqualTerm.iden_comp
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [lift_weaken_from]
        rw [lift_weaken_from]
        rw [extend_insert_into_context]
        rw [←shift_weaken_from]
        rw [extend_insert_into_context]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        rw [←shift_weaken_from]
        rw [←shift_weaken_from]
        rw [weakening_shift_id]
        rw [←helper_weak_iden_propagate_weak]
        rw [extend_insert_into_context]
        apply ihB
        rw [extend_get_sub_context]
        rw [extend_get_sub_context]
        rw [extend_get_sub_context]
        apply hS
        any_goals omega
      · rw [helper_weak_refl_propagate_weak]
        rw [←weak_subst_iden_elim]
        apply ihbB
        apply hS
      · apply ihaA
        apply hS
      · rw [helper_weak_refl_propagate_weak]
        rw [←weak_subst_iden_elim]
        apply ihB'
        apply hS
    case IsEqualTermUnitIntroEq =>
      intro n Γ hiC ihiC l hleq S hS
      apply IsEqualTerm.unit_intro_eq
      apply ihiC
      apply hS
    case IsEqualTermUnitElimEq =>
      intro n Γ A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 l hleq S hS
      rw [weak_sub_zero]
      apply IsEqualTerm.unit_elim_eq
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [←weakening_unit]
        rw [extend_insert_into_context]
        · apply ihAA
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
      · simp [lift_weak_n]
        simp [lift_single_subst_tt]
        apply ihaaA
        apply hS
      · apply ihbb1
        apply hS
    case IsEqualTermEmptyElimEq =>
      intro n Γ A A' b b' hAA hbb0 ihAA ihbb0 l hleq S hS
      rw [weak_sub_zero]
      apply IsEqualTerm.empty_elim_eq
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [←weakening_empty]
        rw [extend_insert_into_context]
        · apply ihAA
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
      · apply ihbb0
        apply hS
    case IsEqualTermPiIntroEq =>
      intro n Γ A A' b b' B B' hbbB hPiPi ihbbB ihPiPi l hleq S hS
      apply IsEqualTerm.pi_intro_eq
      · rw [extend_insert_into_context]
        simp [lift_weak_n]
        rw [lift_weaken_from]
        · apply ihbbB
          simp [get_sub_context]
          split
          · exact hS
          · omega
        · omega
      · apply ihPiPi
        apply hS
    case IsEqualTermPiElimEq =>
      intro n Γ f f' A B a a' hffPi haaA ihffPi ihaaA l hleq s hS
      rw [weak_sub_zero]
      apply IsEqualTerm.pi_elim_eq
      · apply ihffPi
        apply hS
      · apply ihaaA
        apply hS
    case IsEqualTermSigmaIntroEq =>
      intro n Γ a a' A b b' B haaA hbbB ihaaA ihbbB l hleq S hS
      apply IsEqualTerm.sigma_intro_eq
      · apply ihaaA
        apply hS
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · simp [weaken_from]
          split
          case a.isTrue h =>
            rw [←weak_sub_zero]
            apply ihbbB
            apply hS
          case a.isFalse h =>
            omega
        · exact hleq
    case IsEqualTermSigmaElimEq =>
      intro n Γ A B A' B' p p' C C' c c' hSiSi hppSi hCC hccC ihSiSi ihppSi ihCC ihccC l hleq S hS
      rw [weak_sub_zero]
      apply IsEqualTerm.sigma_elim_eq
      · apply ihSiSi
        apply hS
      · apply ihppSi
        apply hS
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · rw (config := {occs := .pos [1]}) [←lift_weaken_from]
          · rw [←weakening_sigma]
            rw [extend_insert_into_context]
            apply ihCC
            rw [extend_get_sub_context]
            apply hS
          · exact hleq
        · exact hleq
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        · rw [lift_weaken_from]
          · rw [weak_subst_sigma_C]
            · simp [extend_insert_into_context]
              apply ihccC
              rw [extend_get_sub_context]
              · rw [extend_get_sub_context]
                apply hS
            · exact hleq
          · omega
        · omega
    case IsEqualTermIdenIntroEq =>
      intro n Γ A A' a a' hAA haaA ihAA ihaaA l hleq S hS
      apply IsEqualTerm.iden_intro_eq
      · apply ihAA
        apply hS
      · apply ihaaA
        apply hS
    case IsEqualTermIdenElimEq =>
      intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' 
      intro hBB hbbB hIdId hppId hB' ihBB ihbbB ihIdId ihppId ihB' l hleq S hS
      rw [weak_subst_iden_elim]
      apply IsEqualTerm.iden_elim_eq
      · simp [lift_weak_n]
        rw [lift_weaken_from]
        rw [lift_weaken_from]
        rw [lift_weaken_from]
        rw [extend_insert_into_context]
        rw [←shift_weaken_from]
        rw [extend_insert_into_context]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        rw [←shift_weaken_from]
        rw [←shift_weaken_from]
        rw [weakening_shift_id]
        rw [←helper_weak_iden_propagate_weak]
        rw [extend_insert_into_context]
        apply ihBB
        rw [extend_get_sub_context]
        rw [extend_get_sub_context]
        rw [extend_get_sub_context]
        apply hS
        any_goals omega
      · rw [helper_weak_refl_propagate_weak]
        rw [←weak_subst_iden_elim]
        apply ihbbB
        apply hS
      · apply ihIdId
        apply hS
      · apply ihppId
        apply hS
      · rw [←weak_subst_iden_elim]
        apply ihB'
        apply hS
    case IsEqualTermUnivUnitEq =>
      intro n Γ hiC ihiC l hleq S hS
      simp [weaken]
      apply IsEqualTerm.univ_unit_eq
      apply ihiC
      apply hS
    case IsEqualTermUnivEmptyEq =>
      intro n Γ hiC ihiC l hleq S hS
      simp [weaken]
      apply IsEqualTerm.univ_empty_eq
      apply ihiC
      apply hS
    case IsEqualTermUnivPiEq =>
      intro n Γ A A' B B' hAAU hBBU ihAAU ihBBU l hleq S hS
      simp [weaken] at *
      simp [lift_weak_n]
      apply IsEqualTerm.univ_pi_eq
      · apply ihAAU
        · apply hS
      · rw [extend_insert_into_context]
        rw [lift_weaken_from]
        apply ihBBU
        simp [get_sub_context]
        split
        · exact hS
        · omega
        omega
    case IsEqualTermUnivSigmaEq =>
      intro n Γ A A' B B' hAAU hBBU ihAAU ihBBU l hleq S hS
      simp [weaken] at *
      simp [lift_weak_n]
      apply IsEqualTerm.univ_sigma_eq
      · apply ihAAU
        · apply hS
      · rw [extend_insert_into_context]
        rw [lift_weaken_from]
        apply ihBBU
        simp [get_sub_context]
        split
        · exact hS
        · omega
        omega
    case IsEqualTermUnivIdenEq =>
      intro n Γ A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' l hleq S hS
      simp [weaken]
      apply IsEqualTerm.univ_iden_eq
      · apply ihAAU
        · apply hS
      · apply ihaaA
        · apply hS
      · apply ihaaA'
        · apply hS
    case IsEqualTermTyConvEq =>
      intro n Γ a b A B habA hAB ihabA ihAB l hleq S hS
      apply IsEqualTerm.ty_conv_eq
      · apply ihabA
        apply hS
      · apply ihAB
        apply hS
    case IsEqualTermTyConvEqSymm =>
      intro n Γ a b A B habA hAB ihabA ihAB l hleq S hS
      apply IsEqualTerm.ty_conv_eq_symm
      · apply ihabA
        apply hS
      · apply ihAB
        apply hS
    case IsEqualTermTermSymm =>
      intro n Γ a a' A haaA ihaaA l hleq S hS
      apply IsEqualTerm.term_symm
      apply ihaaA
      apply hS
    case IsEqualTermTermTrans =>
      intro n Γ T a b C habT hbcT ihabT ihbcT l hleq S hS
      apply IsEqualTerm.term_trans
      · apply ihabT
        apply hS
      · apply ihbcT
        apply hS
