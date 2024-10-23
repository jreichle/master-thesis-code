import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules
import IMLTT.proofs.admissable.Weakening
import IMLTT.proofs.admissable.Substitution

/- # Γ ⊢ J → Γ ctx -/

theorem ctx_decr : IsCtx (Γ ⬝ A) → IsCtx Γ :=
  by
    intro hiCA
    match hiCA with
    | .extend hiC _ => apply hiC

theorem ctx_extr : IsCtx (Γ ⬝ A) → IsType Γ A :=
  by
    intro hiCA
    match hiCA with
    | .extend _ hA => apply hA

theorem boundary_ctx_term' : HasType Γ a A → IsCtx Γ :=
  by
    intro haA
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ _A _hA => IsCtx Γ)
      (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
      (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
      (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
      haA
    any_goals
      solve
      | repeat'
        first
        | intro
        | assumption
    · apply IsCtx.empty
    · apply IsCtx.extend
      any_goals assumption
    · apply IsCtx.extend
      any_goals assumption
    · sorry
    · sorry
    · sorry

theorem boundary_ctx_term : HasType Γ a A → IsCtx Γ :=
    fun haA ↦
      HasType.recOn
        (motive_1 := fun Γ _hiC => IsCtx Γ)
        (motive_2 := fun Γ _A _hA => IsCtx Γ)
        (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
        (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
        (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
        haA
        (IsCtx.empty)
        (fun _hiC hA ihC _ihA ↦ IsCtx.extend ihC hA)
        (fun hiC _hA ↦ hiC)
        (fun hiC _hA ↦ hiC)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _haA _haA' iha _iha' ↦ iha)
        (fun hiC _ihC ↦ hiC)
        (fun _hAU ihAU ↦ ihAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun hiC _ihC ↦ hiC)
        (fun _hbB ihbB ↦ ctx_decr ihbB)
        (fun _haA _hbB ihaA _ihbB ↦ ihaA)
        (fun _haA ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _haA _haA' _ihAU ihaA _ihaA' ↦ ihaA)
        (fun _hA _haA _hb1 _ihA ihaA _ihb1 ↦ ihaA)
        (fun _hA _hb0 _ihA ihb0 ↦ ihb0)
        (fun _hfPi _haA _ihfPi ihaA ↦ ihaA)
        (fun _hpSi _hC _hcC ihpSi _ihC _ihcC ↦ ihpSi)
        (fun _hB _hbB _hpId _ihB _ihbB ihpId ↦ ihpId)
        (fun _haA _hAB ihaA _ihAB ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _haaA _haaA' ihaaA _ihaaA' ↦ ihaaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU ihAAU ↦ ihAAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun _hA _haA _ihA ihaA  ↦ ihaA)
        (fun _hbB _haA _ihbB ihaA ↦ ihaA)
        (fun _haA _hbB _hC _hcC ihaA _ihbB _ihC _ihcC ↦ ihaA)
        (fun _hB _hbB _haA _ihB _ihbB ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _haaA _hbb1 _ihAA ihaaA _ihbb1 ↦ ihaaA)
        (fun _hAA _hbb0 _ihAA ihbb0 ↦ ihbb0)
        (fun _hbbB ihbbB ↦ ctx_decr ihbbB)
        (fun _haaA _hffPi ihaaA _ihffPi ↦ ihaaA)
        (fun _haaA _hbbB ihaaA _ihbbB ↦ ihaaA)
        (fun _hSiSi _hppSi _hCC _hccC ihSiSi _ihppSi _ihCC _ihccC ↦ ihSiSi)
        (fun _haaA ihaaA ↦ ihaaA)
        (fun _hBB _hbbB _hppId _ihBB _ihbbB ihppId ↦ ihppId)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _haaA _haaA' _ihAAU ihaaA _ihaaA' ↦ ihaaA)
        (fun _habA _hAB ihabA _ihAB ↦ ihabA)

  theorem boundary_ctx_type : IsType Γ A → IsCtx Γ :=
    fun hA ↦
      IsType.recOn
        (motive_1 := fun Γ _hiC => IsCtx Γ)
        (motive_2 := fun Γ _A _hA => IsCtx Γ)
        (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
        (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
        (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
        hA
        (IsCtx.empty)
        (fun _hiC hA ihC _ihA ↦ IsCtx.extend ihC hA)
        (fun hiC _hA ↦ hiC)
        (fun hiC _hA ↦ hiC)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _haA _haA' iha _iha' ↦ iha)
        (fun hiC _ihC ↦ hiC)
        (fun _hAU ihAU ↦ ihAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun hiC _ihC ↦ hiC)
        (fun _hbB ihbB ↦ ctx_decr ihbB)
        (fun _haA _hbB ihaA _ihbB ↦ ihaA)
        (fun _haA ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _haA _haA' _ihAU ihaA _ihaA' ↦ ihaA)
        (fun _hA _haA _hb1 _ihA ihaA _ihb1 ↦ ihaA)
        (fun _hA _hb0 _ihA ihb0 ↦ ihb0)
        (fun _hfPi _haA _ihfPi ihaA ↦ ihaA)
        (fun _hpSi _hC _hcC ihpSi _ihC _ihcC ↦ ihpSi)
        (fun _hB _hbB _hpId _ihB _ihbB ihpId ↦ ihpId)
        (fun _haA _hAB ihaA _ihAB ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _haaA _haaA' ihaaA _ihaaA' ↦ ihaaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU ihAAU ↦ ihAAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun _hA _haA _ihA ihaA  ↦ ihaA)
        (fun _hbB _haA _ihbB ihaA ↦ ihaA)
        (fun _haA _hbB _hC _hcC ihaA _ihbB _ihC _ihcC ↦ ihaA)
        (fun _hB _hbB _haA _ihB _ihbB ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _haaA _hbb1 _ihAA ihaaA _ihbb1 ↦ ihaaA)
        (fun _hAA _hbb0 _ihAA ihbb0 ↦ ihbb0)
        (fun _hbbB ihbbB ↦ ctx_decr ihbbB)
        (fun _haaA _hffPi ihaaA _ihffPi ↦ ihaaA)
        (fun _haaA _hbbB ihaaA _ihbbB ↦ ihaaA)
        (fun _hSiSi _hppSi _hCC _hccC ihSiSi _ihppSi _ihCC _ihccC ↦ ihSiSi)
        (fun _haaA ihaaA ↦ ihaaA)
        (fun _hBB _hbbB _hppId _ihBB _ihbbB ihppId ↦ ihppId)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _haaA _haaA' _ihAAU ihaaA _ihaaA' ↦ ihaaA)
        (fun _habA _hAB ihabA _ihAB ↦ ihabA)

  theorem boundary_ctx_type_eq : IsEqualType Γ A A' → IsCtx Γ :=
    fun hAA ↦
      IsEqualType.recOn
        (motive_1 := fun Γ _hiC => IsCtx Γ)
        (motive_2 := fun Γ _A _hA => IsCtx Γ)
        (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
        (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
        (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
        hAA
        (IsCtx.empty)
        (fun _hiC hA ihC _ihA ↦ IsCtx.extend ihC hA)
        (fun hiC _hA ↦ hiC)
        (fun hiC _hA ↦ hiC)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _haA _haA' iha _iha' ↦ iha)
        (fun hiC _ihC ↦ hiC)
        (fun _hAU ihAU ↦ ihAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun hiC _ihC ↦ hiC)
        (fun _hbB ihbB ↦ ctx_decr ihbB)
        (fun _haA _hbB ihaA _ihbB ↦ ihaA)
        (fun _haA ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _haA _haA' _ihAU ihaA _ihaA' ↦ ihaA)
        (fun _hA _haA _hb1 _ihA ihaA _ihb1 ↦ ihaA)
        (fun _hA _hb0 _ihA ihb0 ↦ ihb0)
        (fun _hfPi _haA _ihfPi ihaA ↦ ihaA)
        (fun _hpSi _hC _hcC ihpSi _ihC _ihcC ↦ ihpSi)
        (fun _hB _hbB _hpId _ihB _ihbB ihpId ↦ ihpId)
        (fun _haA _hAB ihaA _ihAB ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _haaA _haaA' ihaaA _ihaaA' ↦ ihaaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU ihAAU ↦ ihAAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun _hA _haA _ihA ihaA  ↦ ihaA)
        (fun _hbB _haA _ihbB ihaA ↦ ihaA)
        (fun _haA _hbB _hC _hcC ihaA _ihbB _ihC _ihcC ↦ ihaA)
        (fun _hB _hbB _haA _ihB _ihbB ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _haaA _hbb1 _ihAA ihaaA _ihbb1 ↦ ihaaA)
        (fun _hAA _hbb0 _ihAA ihbb0 ↦ ihbb0)
        (fun _hbbB ihbbB ↦ ctx_decr ihbbB)
        (fun _haaA _hffPi ihaaA _ihffPi ↦ ihaaA)
        (fun _haaA _hbbB ihaaA _ihbbB ↦ ihaaA)
        (fun _hSiSi _hppSi _hCC _hccC ihSiSi _ihppSi _ihCC _ihccC ↦ ihSiSi)
        (fun _haaA ihaaA ↦ ihaaA)
        (fun _hBB _hbbB _hppId _ihBB _ihbbB ihppId ↦ ihppId)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _haaA _haaA' _ihAAU ihaaA _ihaaA' ↦ ihaaA)
        (fun _habA _hAB ihabA _ihAB ↦ ihabA)

theorem boundary_ctx_term_eq : IsEqualTerm Γ a b A → IsCtx Γ :=
    fun haaA ↦
      IsEqualTerm.recOn
        (motive_1 := fun Γ _hiC => IsCtx Γ)
        (motive_2 := fun Γ _A _hA => IsCtx Γ)
        (motive_3 := fun Γ _a _A _haA => IsCtx Γ)
        (motive_4 := fun Γ _A _A' _hAA => IsCtx Γ)
        (motive_5 := fun Γ _a _a' _A _haaA => IsCtx Γ)
        haaA
        (IsCtx.empty)
        (fun _hiC hA ihC _ihA ↦ IsCtx.extend ihC hA)
        (fun hiC _hA ↦ hiC)
        (fun hiC _hA ↦ hiC)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _hA _hB ihA _ihB ↦ ihA)
        (fun _haA _haA' iha _iha' ↦ iha)
        (fun hiC _ihC ↦ hiC)
        (fun _hAU ihAU ↦ ihAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun hiC _ihC ↦ hiC)
        (fun _hbB ihbB ↦ ctx_decr ihbB)
        (fun _haA _hbB ihaA _ihbB ↦ ihaA)
        (fun _haA ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _hBU ihAU _ihBU ↦ ihAU)
        (fun _hAU _haA _haA' _ihAU ihaA _ihaA' ↦ ihaA)
        (fun _hA _haA _hb1 _ihA ihaA _ihb1 ↦ ihaA)
        (fun _hA _hb0 _ihA ihb0 ↦ ihb0)
        (fun _hfPi _haA _ihfPi ihaA ↦ ihaA)
        (fun _hpSi _hC _hcC ihpSi _ihC _ihcC ↦ ihpSi)
        (fun _hB _hbB _hpId _ihB _ihbB ihpId ↦ ihpId)
        (fun _haA _hAB ihaA _ihAB ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _hAA _hBB ihAA _ihBB ↦ ihAA)
        (fun _haaA _haaA' ihaaA _ihaaA' ↦ ihaaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU ihAAU ↦ ihAAU)
        (fun hA ihA ↦ IsCtx.extend ihA hA)
        (fun _hA _haA _ihA ihaA  ↦ ihaA)
        (fun _hbB _haA _ihbB ihaA ↦ ihaA)
        (fun _haA _hbB _hC _hcC ihaA _ihbB _ihC _ihcC ↦ ihaA)
        (fun _hB _hbB _haA _ihB _ihbB ihaA ↦ ihaA)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAA _haaA _hbb1 _ihAA ihaaA _ihbb1 ↦ ihaaA)
        (fun _hAA _hbb0 _ihAA ihbb0 ↦ ihbb0)
        (fun _hbbB ihbbB ↦ ctx_decr ihbbB)
        (fun _haaA _hffPi ihaaA _ihffPi ↦ ihaaA)
        (fun _haaA _hbbB ihaaA _ihbbB ↦ ihaaA)
        (fun _hSiSi _hppSi _hCC _hccC ihSiSi _ihppSi _ihCC _ihccC ↦ ihSiSi)
        (fun _haaA ihaaA ↦ ihaaA)
        (fun _hBB _hbbB _hppId _ihBB _ihbbB ihppId ↦ ihppId)
        (fun hiC _ihiC ↦ hiC)
        (fun hiC _ihiC ↦ hiC)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _hBBU ihAAU _ihBBU ↦ ihAAU)
        (fun _hAAU _haaA _haaA' _ihAAU ihaaA _ihaaA' ↦ ihaaA)
        (fun _habA _hAB ihabA _ihAB ↦ ihabA)

/- # if hasType, then type is well-formed -/

theorem lambda_from : HasType Γ f (.pi A B) → ∃b, (HasType (Γ ⬝ A) b B) :=
  by
    intro hfPi
    match hfPi with
    | _ => sorry

theorem boundary_term_type : HasType Γ a A → IsType Γ A :=
  by
    intro haA
    match haA with
    | .var hA =>
      apply weakening_type hA hA
    | .unit_intro hiC =>
      apply IsType.unit_form hiC
    | .pi_intro hbB =>
      have hB := boundary_term_type hbB
      apply IsType.pi_form 
      · have hiCA := boundary_ctx_type hB
        apply ctx_extr hiCA
      · apply hB
    | .sigma_intro haA hbB =>
      apply IsType.sigma_form
      · apply boundary_term_type haA
      · have hBs := boundary_term_type hbB
        apply substitution_inv_type 
        · rfl
        · apply hBs
        · apply haA
    | .iden_intro haA =>
      apply IsType.iden_form haA haA
    -- univ start
    | .univ_unit hiC => 
      apply IsType.univ_form hiC
    | .univ_empty hiC =>
      apply IsType.univ_form hiC
    | .univ_pi hAU hBU =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    | .univ_sigma hAU hBU =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    | .univ_iden hAU haA haA' =>
      have hiC := boundary_ctx_term hAU
      apply IsType.univ_form hiC
    -- univ end
    | .unit_elim hA haA hb1 =>
      apply substitution_type
      · apply hb1
      · apply hA
    | .empty_elim hA hb0 =>
      apply substitution_type
      · apply hb0
      · apply hA
    | .pi_elim hfPi haA =>
      apply substitution_type
      · apply haA
      · sorry
    | .sigma_elim hpPi hC hcC =>
      apply substitution_type
      · apply hpPi
      · apply hC
    | .iden_elim hB hbB hpI =>
      sorry
    | .ty_conv haA hAB =>
      sorry

#print Exists.elim

theorem boundary_equal_term_type : IsEqualTerm Γ a a' A → IsType Γ A :=
  sorry

/-# if substiution works, then adding type to context also -/

theorem boundary_subs_type_ctx : IsType Γ (substitute A (.extend σ b))  → HasType Γ b B
                                 → IsType (Γ ⬝ B) (substitute A (.lift (σ))) :=
  sorry
