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
import IMLTT.typed.proofs.admissable.WeakeningGeneral

import IMLTT.typed.proofs.admissable.substitution.Helpers
import IMLTT.typed.proofs.admissable.substitution.IsCtx
import IMLTT.typed.proofs.admissable.substitution.IsType
import IMLTT.typed.proofs.admissable.substitution.HasType
import IMLTT.typed.proofs.admissable.substitution.IsEqualType
import IMLTT.typed.proofs.admissable.substitution.IsEqualTerm

set_option pp.proofs true

theorem helper_weaken_k_from : n + k + 1 = n + 1 + k := by omega

def weaken_k_from (k : Nat) (n : Nat) (l : Nat) : Weak (n + k) n :=
  match n with
  | .zero => shift_weak_n k .id
  | .succ n' =>
    if l < n' + 1 then
      helper_weaken_k_from ▸ .lift (weaken_k_from k n' l)
    else
      shift_weak_n k .id

def n_substitution_shift {l n : Nat} (leq : l ≤ n) (a : Tm l) : Subst n n :=
  match n with
  | .zero =>
    .weak .id
  | .succ n' =>
    if h : l < n' + 1 then
      .lift (n_substitution_shift (Nat.le_of_lt_succ h) a)
    else
      have heq : l = Nat.succ n' := substitute_n_helper leq h
      .extend (.weak (.shift .id)) (heq ▸ a)

def substitute_shift_into_gen_ctx
    (s : Tm l) (Δ : CtxGen m n) (leq : l ≤ m) : CtxGen m n :=
  match Δ with
  | .start => CtxGen.start
  | .expand (n:= n) Δ' T =>
    have h :  m ≤ n := gen_ctx_leq Δ'
    have h1 : l ≤ n := by omega
    .expand (substitute_shift_into_gen_ctx s Δ' leq) (substitute (n_substitution_shift h1 s) T)

notation:95 a "↑/ₙ" le => n_substitution_shift le a
notation:95 "⌈" s "↑⌉(" Δ "w/" leq ")" => substitute_shift_into_gen_ctx s Δ leq

theorem substitution :
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {s S : Tm l},
    (Γ ⬝ S ⊗ Δ) ctx → (Γ ⊢ s ∶ S)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ctx) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {A : Tm n} {s S : Tm l},
    (Γ ⬝ S ⊗ Δ) ⊢ A type → (Γ ⊢ s ∶ S)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ A⌈s↑/ₙleq⌉ type) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A a : Tm (n)} {s S : Tm l},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ∶ A) → (Γ ⊢ s ∶ S)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A A' : Tm (n)} {s S : Tm l},
    (Γ ⬝ S ⊗ Δ) ⊢ A ≡ A' type → (Γ ⊢ s ∶ S)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) ∧
  (∀ {n l : Nat} {leq : l ≤ n} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A a a' : Tm (n)} {s S : Tm l},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⊢ s ∶ S)
    → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) :=
  by
    suffices h :
        (∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s S : Tm l),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {s S : Tm l} (A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ A_1⌈s↑/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s S : Tm l)
              (a_1 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_1 →
                  eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ a_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
            Γ ⊢ A ≡ A' type →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s S : Tm l)
                (A_1 A'_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    eqM ▸ A' = A'_1 →
                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
            (Γ ⊢ a ≡ a' ∶ A) →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s S : Tm l)
                (a_1 a'_1 A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a = a_1 →
                    eqM ▸ a' = a'_1 →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⊢ s ∶ S) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l) ⊢ a_1⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉
      by
        sorry
        -- any_goals repeat' (apply And.intro)
        -- · intro n l hleq Γ Δ s S hiC hsS
        --   apply (And.left h)
        --   · apply hiC
        --   · apply hleq
        --   · rfl
        --   · apply hsS
        --   · rfl
        -- · intro n l hleq Γ Δ A s S hA hsS
        --   apply And.left (And.right h)
        --   · apply hA
        --   · rfl
        --   · rfl
        --   · apply hsS
        --   · rfl
        -- · intro n l hleq Γ Δ A a s S haA hsS
        --   apply And.left (And.right (And.right h))
        --   · apply haA
        --   · rfl
        --   · rfl
        --   · rfl
        --   · apply hsS
        --   · rfl
        -- · intro n l hleq Γ Δ A A' s S hAA hsS
        --   apply And.left (And.right (And.right (And.right h)))
        --   · apply hAA
        --   · rfl
        --   · rfl
        --   · rfl
        --   · apply hsS
        --   · rfl
        -- · intro n l hleq Γ Δ A a a' s S haaA hsS
        --   apply And.right (And.right (And.right (And.right h)))
        --   · apply haaA
        --   · rfl
        --   · rfl
        --   · rfl
        --   · rfl
        --   · apply hsS
        --   · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → (Γ ⊢ s ∶ S)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) {s S : Tm l} A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = A
        → (Γ ⊢ s ∶ S)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ A⌈s↑/ₙleq⌉ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S a A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = a → eqM ▸ A' = A
        → (Γ ⊢ s ∶ S)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉)
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S A A',
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ C = A → eqM ▸ C' = A'
        → (Γ ⊢ s ∶ S)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ A⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type)
      (motive_5 := fun {n} Γ' c c' C _haaA =>
        ∀ m l {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) s S a a' A,
        eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → (Γ ⊢ s ∶ S)
        → (Γ ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_succ l)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉)
    case IsTypePiForm =>
      sorry
    case HasTypeVar =>
      sorry
    any_goals sorry
