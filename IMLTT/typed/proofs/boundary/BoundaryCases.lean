import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

mutual
  theorem boundary_is_type_type_eq {n : Nat} {Γ : Ctx n} {S S' : Tm n} :
      IsEqualType Γ S S' → IsType Γ S := 
    by
      intro hSS
      cases S
      case unit =>
        cases hSS with
        | unit_form_eq h =>
          constructor
          exact h
        | univ_elim_eq h =>
          constructor
          apply boundary_ctx_term_eq h
        | refl =>
          sorry
        | symm =>
          sorry
        | trans =>
          sorry
      case empty =>
        cases hSS with
        | empty_form_eq h =>
          constructor
          exact h
        | univ_elim_eq h =>
          constructor
          apply boundary_ctx_term_eq h
        | refl =>
          sorry
        | symm =>
          sorry
        | trans =>
          sorry
      case pi A B =>
        cases hSS with
        | pi_form_eq hAA' hBB' =>
          constructor
          · exact boundary_is_type_type_eq hAA'
          · exact boundary_is_type_type_eq hBB'
        | univ_elim_eq h =>
          have hPiU := boundary_has_type_term_eq h
          exact IsType.univ_elim hPiU
        | refl =>
          sorry
        | symm =>
          sorry
        | trans =>
          sorry
      any_goals sorry
      -- case sigma A B =>
      --   cases hSS with
      --   | sigma_form_eq hAA' hBB' =>
      --     constructor
      --     · exact boundary_is_type_type_eq hAA'
      --     · exact boundary_is_type_type_eq hBB'
      --   | refl =>
      --     sorry
      --   | symm =>
      --     sorry
      --   | trans =>
      --     sorry
      --   | univ_elim_eq h =>
      --     have hSiU := boundary_has_type_term_eq h
      --     have hInv := sigma_has_type_inversion hSiU
      --     constructor
      --     · exact IsType.univ_elim (And.left hInv)
      --     · exact IsType.univ_elim (And.right hInv)
      -- case iden A a a' =>
      --   cases hSS with
      --   | iden_form_eq hAA haaA haaA' =>
      --     constructor
      --     · exact boundary_has_type_term_eq haaA
      --     · exact HasType.ty_conv (boundary_has_type_term_eq haaA') (IsEqualType.symm hAA)
      --   | univ_elim_eq h =>
      --     have hIdU := boundary_has_type_term_eq h
      --     have hInv := iden_has_type_inversion hIdU
      --     constructor
      --     · exact And.left (And.right hInv)
      --     · exact And.right (And.right hInv)
      --   | refl =>
      --     sorry
      --   | symm =>
      --     sorry
      --   | trans =>
      --     sorry
      -- case univ =>
      --   cases hSS with
      --   | univ_form_eq hiC =>
      --     constructor
      --     exact hiC
      --   | univ_elim_eq h =>
      --     constructor
      --     apply boundary_ctx_term_eq h
      --   | refl =>
      --     sorry
      --   | symm =>
      --     sorry
      --   | trans =>
      --     sorry
      -- case var =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case tt =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case indUnit =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case indEmpty =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case lam =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case app =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case pairSigma =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case indSigma =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case refl =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry
      -- case j =>
      --   cases hSS
      --   case univ_elim_eq h =>
      --     constructor
      --     exact boundary_has_type_term_eq h
      --   case refl =>
      --     sorry
      --   case symm =>
      --     sorry
      --   case trans =>
      --     sorry

  theorem boundary_has_type_term_eq {n : Nat} {Γ : Ctx n} {s s' S : Tm n} :
      IsEqualTerm Γ s s' S → HasType Γ s S :=
    by
      intro hssS
      -- both cases on s and S not possible - terrmination error for self reference inside unit case
      cases S
      case unit =>
        cases hssS
        case var_eq h1 h2 =>
          constructor
          · assumption
          · assumption
        case unit_comp h1 h2 h3 =>
          constructor
          · exact h1
          · exact h2
          · constructor
            exact boundary_ctx_term h2
          · exact h3
        case pi_comp h1 h2 h3 h4 =>
          constructor
          · constructor
            exact h1
          · exact h2
          · exact h4
        case sigma_comp h1 h2 h3 h4 h5 h6 =>
          constructor
          · constructor
            · exact h1
            · exact h2
          · exact h3
          · exact h4
          · exact h6
        case iden_comp h1 h2 h3 h4 h5 =>
          constructor
          · exact h1
          · exact h4
          · constructor
            exact h2
          · exact h3
          · exact h5
        case unit_intro_eq h1 =>
          constructor
          assumption
        case unit_elim_eq h1 h2 h3 h4 =>
          constructor
          · exact boundary_is_type_type_eq h1
          · sorry
          · sorry
          · sorry
        any_goals sorry
      -- cases hssS
      -- case var_eq hA hEq =>
      --   constructor
      --   · exact hA
      --   · exact hEq
      -- case unit_comp h1 h2 h3 =>
      --   constructor
      --   · exact h1
      --   · exact h2
      --   · constructor
      --     exact boundary_ctx_term h2
      --   · exact h3
      -- case pi_comp h1 h2 h3 h4 =>
      --   constructor
      --   · constructor
      --     exact h1
      --   · exact h2
      --   · exact h4
      -- case sigma_comp h1 h2 h3 h4 h5 h6 =>
      --   constructor
      --   · constructor
      --     · exact h1
      --     · exact h2
      --   · exact h3
      --   · exact h4
      --   · exact h6
      -- case iden_comp h1 h2 h3 h4 =>
      --   constructor
      --   · exact h1
      --   · exact h3
      --   · constructor
      --     exact h2
      --   · exact boundary_is_type_term h3
      --   · exact h4
      -- case unit_intro_eq h1 =>
      --   constructor
      --   exact h1
      -- case pi_intro_eq h1 h2 =>
      --   constructor
      --   exact boundary_has_type_term_eq h1 -- termination error
      any_goals sorry

  theorem boundary_is_type_type_eq' : IsEqualType Γ A A' → IsType Γ A' :=
    by
      intro hAA
      sorry

  theorem boundary_has_type_term_eq' : IsEqualTerm Γ a a' A → HasType Γ a' A :=
    by
      intro haaA
      sorry

  theorem boundary_is_type_term {n : Nat} {Γ : Ctx n} {s S : Tm n} :
      HasType Γ s S → IsType Γ S := 
    by
      intro hsS
      cases S
      case unit =>
        constructor
        apply boundary_ctx_term hsS
      case empty =>
        constructor
        apply boundary_ctx_term hsS
      case pi A B =>
        cases hsS
        case pi_intro hbB =>
          apply IsType.pi_form
          · apply ctx_extr (boundary_ctx_term hbB)
          · apply boundary_is_type_term hbB
        case var n Γ A hA hEq =>
          rw [hEq]
          apply weakening_type
          · apply hA
          · apply hA
        case unit_elim A a b hA haA hb1 hEq =>
          rw [hEq]
          apply substitution_type
          · apply hb1
          · apply hA
        case empty_elim A b hA hb0 hEq =>
          rw [hEq]
          apply substitution_type
          · apply hb0
          · apply hA
        case pi_elim A B a haPi haA hEq =>
          rw [hEq]
          have hPi := boundary_is_type_term haPi
          have hPiInv := pi_is_type_inversion hPi
          apply substitution_type
          · apply haA
          · apply And.right hPiInv
        case sigma_elim hpSi hC hcC hEq =>
          rw [hEq]
          apply substitution_type
          · apply hpSi
          · apply hC
        case iden_elim hB hbB hpId hB' hEq =>
          rw [hEq]
          apply hB'
        case ty_conv hsA hAPi =>
          apply boundary_is_type_type_eq' hAPi
      case sigma A B =>
        cases hsS
        case sigma_intro haA hbB =>
          apply IsType.sigma_form
          · apply boundary_is_type_term haA
          · apply substitution_inv_type
            · rfl
            · apply boundary_is_type_term hbB
            · apply haA
        case var n Γ A hA hEq =>
          rw [hEq]
          apply weakening_type
          · apply hA
          · apply hA
        case unit_elim A a b hA haA hb1 hEq =>
          rw [hEq]
          apply substitution_type
          · apply hb1
          · apply hA
        case empty_elim A b hA hb0 hEq =>
          rw [hEq]
          apply substitution_type
          · apply hb0
          · apply hA
        case pi_elim A B a haPi haA hEq =>
          rw [hEq]
          have hPi := boundary_is_type_term haPi
          have hPiInv := pi_is_type_inversion hPi
          apply substitution_type
          · apply haA
          · apply And.right hPiInv
        case sigma_elim hpSi hC hcC hEq =>
          rw [hEq]
          apply substitution_type
          · apply hpSi
          · apply hC
        case iden_elim hB hbB hpId hB' hEq =>
          rw [hEq]
          apply hB'
        case ty_conv hsA hAPi =>
          apply boundary_is_type_type_eq' hAPi
      case iden A a a' =>
        cases hsS
        case iden_intro haA =>
          apply IsType.iden_form
          · apply haA
          · apply haA
        case var n Γ A hA hEq =>
          rw [hEq]
          apply weakening_type
          · apply hA
          · apply hA
        case unit_elim A a b hA haA hb1 hEq =>
          rw [hEq]
          apply substitution_type
          · apply hb1
          · apply hA
        case empty_elim A b hA hb0 hEq =>
          rw [hEq]
          apply substitution_type
          · apply hb0
          · apply hA
        case pi_elim A B a haPi haA hEq =>
          rw [hEq]
          have hPi := boundary_is_type_term haPi
          have hPiInv := pi_is_type_inversion hPi
          apply substitution_type
          · apply haA
          · apply And.right hPiInv
        case sigma_elim hpSi hC hcC hEq =>
          rw [hEq]
          apply substitution_type
          · apply hpSi
          · apply hC
        case iden_elim hB hbB hpId hB' hEq =>
          rw [hEq]
          apply hB'
        case ty_conv hsA hAPi =>
          apply boundary_is_type_type_eq' hAPi
      case univ =>
        constructor
        apply boundary_ctx_term hsS
      case var x => -- TODO: would need proof that terms cannot be types by themselves
        cases hsS
        any_goals sorry
      case tt =>
        sorry -- inversion lemma s ∶ ⋆ → false
      any_goals sorry

  theorem boundary_is_type_term_eq {n : Nat} {Γ : Ctx n} {s s' S : Tm n} :
      IsEqualTerm Γ s s' S → IsType Γ S :=
    by
      intro hssS
      sorry
end
