import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution

theorem empty_insert_into_context :
    insert_into_ctx (leq := Nat.le_refl 0) ε B = ε ⬝ B :=
  by
    aesop

theorem head_insert_into_context {n : Nat} {Γ : Ctx n} {B : Tm n} :
    Γ ⬝ B = insert_into_ctx (leq := Nat.le_refl n) Γ B :=
  by
    cases Γ with
    | empty =>
      apply empty_insert_into_context
    | extend Γ' t =>
      simp [insert_into_ctx]

theorem middle_insert_into_context {n : Nat} {Γ : Ctx n} {A S : Tm n} :
    Γ ⬝ S ⬝ A⌊↑ₚidₚ⌋ = insert_into_ctx (leq := Nat.le_succ n) (Γ ⬝ A) S :=
  by
    simp [insert_into_ctx]
    apply And.intro
    · rw [head_insert_into_context]
    · rw [←weaken_from_zero]
      omega

theorem extend_insert_into_context {leq : l ≤ n} {Γ : Ctx n} :
    insert_into_ctx (leq := leq) Γ S ⬝ A⌊weaken_from n l⌋ = insert_into_ctx (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) S :=
  by
    cases n with
    | zero =>
      cases l with
      | zero =>
        simp [insert_into_ctx]
      | succ l' =>
        simp [insert_into_ctx]
        apply False.elim
        omega
    | succ n' =>
      simp [insert_into_ctx]
      split
      · simp [insert_into_ctx]
        apply And.intro
        · apply False.elim
          omega
        · apply False.elim
          omega
      · case isFalse h1 =>
        simp [weaken_from]

theorem empty_get_sub_context {leq : l = 0} :
    get_sub_context (leq := Nat.le_of_eq leq) ε l = leq ▸ ε :=
  by
    aesop

theorem extend_get_sub_context {leq : l <= n} {Γ : Ctx n} :
    get_sub_context (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) l = get_sub_context (leq := leq) Γ l :=
  by
    simp [get_sub_context]
    split
    case isTrue h =>
      rfl
    case isFalse h =>
      omega

theorem head_get_sub_context {eq : l = n} {Γ : Ctx n} :
    get_sub_context (leq := Nat.le_of_eq eq) Γ l = eq ▸ Γ :=
  by
    cases n with
    | zero =>
      cases l with
      | zero =>
        simp [get_sub_context]
        cases Γ with
        | empty =>
          rfl
      | succ l' =>
        omega
    | succ n' =>
      cases l with
      | zero =>
        omega
      | succ l' =>
        simp [get_sub_context]
        split
        case succ.succ.isTrue hT =>
          omega
        case succ.succ.isFalse hF =>
          rfl

theorem head_get_from_context {eq : l = n} {Γ : Ctx n} :
    get_from_context (leq := Nat.le_of_eq eq) (Γ ⬝ A) l = eq ▸ A :=
  by
    simp [get_from_context]
    split
    case isTrue h =>
      rfl
    case isFalse h =>
      omega

theorem extend_get_from_context {leq : l <= n} {Γ : Ctx (n + 1)} :
    get_from_context (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) l = get_from_context (leq := leq) Γ l :=
  by
    simp [get_from_context]
    split
    case isTrue h =>
      omega
    case isFalse h =>
      rfl

theorem head_remove_from_context {eq : l = n} {Γ : Ctx n} :
    remove_from_ctx (l := l) (leq := Nat.le_of_eq eq) (Γ ⬝ A) s = Γ :=
  by
    simp [remove_from_ctx]
    intro neq
    omega

theorem extend_remove_from_context {leq : l ≤ n} {Γ : Ctx (n + 1)} {s : Tm l}:
    remove_from_ctx (leq := leq) Γ s ⬝ A⌈n_substitution (leq := leq) s⌉ = remove_from_ctx (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) s :=
  by
    simp [remove_from_ctx]
    split
    case isTrue hT =>
      omega
    case isFalse hF =>
      rfl

theorem empty_expand_context {n : Nat} {Γ : Ctx n} :
    Γ ⊗ CtxGen.start = Γ :=
  by
    simp [expand_ctx]

theorem extend_expand_context {Γ : Ctx l} {Δ : CtxGen (l) n} {A : Tm n}:
    (Γ ⊗ Δ) ⬝ A =
    Γ ⊗ (Δ ⊙ A) :=
  by
    induction Δ
    case start =>
      simp [expand_ctx]
    case expand Δ T =>
      simp [expand_ctx]

theorem empty_extend_expand_context_n_substitution {n : Nat} {Γ : Ctx n} {s : Tm n} :
    Γ ⊗ ⌈s⌉(CtxGen.start w/ (Nat.le_refl n)) =
    Γ ⊗ CtxGen.start :=
  by
    simp [substitute_into_gen_ctx]

theorem extend_expand_context_n_substitution' {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {A : Tm (n + 1)}:
    (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⬝ (A)⌈s/ₙ(gen_ctx_leq_sub Δ)⌉ =
    Γ ⊗ ⌈s⌉((Δ ⊙ A) w/Nat.le_refl l) :=
  by
    rw [substitute_into_gen_ctx]
    cases Δ
    case start =>
      rw [expand_ctx]
    case expand Δ T =>
      rw [expand_ctx]

theorem extend_expand_context_n_substitution {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A : Tm n}:
    (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⬝ (ht_ext_exp_n (neq := gen_ctx_neq Δ) ▸ A)⌈s/ₙ(gen_ctx_leq_sub Δ)⌉ =
    ht_ext_exp_n_extr (neq := gen_ctx_neq Δ) ▸ Γ ⊗ ⌈s⌉((Δ ⊙ A) w/Nat.le_refl l) :=
  by
    rw [substitute_into_gen_ctx]
    induction Δ
    case start =>
      rw [expand_ctx]
    case expand Δ T =>
      rw [expand_ctx]
