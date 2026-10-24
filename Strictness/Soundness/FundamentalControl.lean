import Strictness.Semantics.EnvironmentLemmas
import Strictness.Semantics.SemanticControl
import Strictness.Semantics.SemanticPlusEnv
import Strictness.Semantics.SemanticPlus
import Strictness.Semantics.SemanticPlusD
import Strictness.Semantics.SemanticCap
import Strictness.Semantics.SemanticSubstitution
import Strictness.Semantics.SemanticSubtype
import Strictness.Soundness.FundamentalRules
import Strictness.Soundness.FundamentalAbs
import Strictness.Soundness.FundamentalApp
import Strictness.Soundness.FundamentalPair
import Strictness.Soundness.FundamentalProj
import Strictness.Language.Erasure
import Strictness.Language.SimpleSubstitution

namespace Strictness

open Usage
open Term

/-- T-Op, V-side. -/
theorem fundamental_op_V
    {Γ Γ₁ Γ₂ : Env} {u₁ u₂ u : Usage} {e₁ e₂ : Term} {ρ : Substitution}
    (hu₁ : u₁ ≤ u) (hu₂ : u₂ ≤ u)
    (hPlus : Env.plus Γ₁ Γ₂ = some Γ)
    (ihV₁ : Valid Γ₁ ρ → V (.int u₁) (Substitution.apply ρ e₁))
    (ihV₂ : Valid Γ₂ ρ → V (.int u₂) (Substitution.apply ρ e₂))
    (hValid : Valid Γ ρ) :
    V (.int u) (Substitution.apply ρ (.op o e₁ e₂)) := by
  have hValidSplit := valid_plus_split_of_semantic semantic_plus_V hPlus hValid
  have hV₁ := ihV₁ hValidSplit.1
  have hV₂ := ihV₂ hValidSplit.2
  simpa [Substitution.apply] using V_op hu₁ hu₂ hV₁ hV₂

/-- T-Op, D-side. -/
theorem fundamental_op_D
    {Γ Γ₁ Γ₂ : Env} {u₁ u₂ u : Usage} {e₁ e₂ : Term} {ρ : Substitution}
    (hu₁ : u₁ ≤ u) (hu₂ : u₂ ≤ u)
    (hPlus : Env.plus Γ₁ Γ₂ = some Γ)
    (ihV₁ : Valid Γ₁ ρ → V (.int u₁) (Substitution.apply ρ e₁))
    (ihD₁ : Valid Γ₁ ρ → SatisfiesD Γ₁ ρ →
      D (.int u₁) (Substitution.apply ρ e₁))
    (ihV₂ : Valid Γ₂ ρ → V (.int u₂) (Substitution.apply ρ e₂))
    (ihD₂ : Valid Γ₂ ρ → SatisfiesD Γ₂ ρ →
      D (.int u₂) (Substitution.apply ρ e₂))
    (hValid : Valid Γ ρ) (hD : SatisfiesD Γ ρ) :
    D (.int u) (Substitution.apply ρ (.op o e₁ e₂)) := by
  have hValidSplit := valid_plus_split_of_semantic semantic_plus_V hPlus hValid
  have hV₁ := ihV₁ hValidSplit.1
  have hV₂ := ihV₂ hValidSplit.2
  rcases satisfiesD_plus_split_of_semantic semantic_plus_D hPlus hD with hD₁ | hD₂
  · have hD₁' := ihD₁ hValidSplit.1 hD₁
    simpa [Substitution.apply] using D_op_left hu₁ hu₂ hD₁' hV₂
  · have hD₂' := ihD₂ hValidSplit.2 hD₂
    simpa [Substitution.apply] using D_op_right hu₁ hu₂ hV₁ hD₂'

theorem fundamental_if_V
    {Γ Γ₀ Γ₁ Γ₂ Γ₁₂ : Env}
    {u : Usage} {τ₁ τ₂ τ : Ty} {e₀ e₁ e₂ : Term} {ρ : Substitution}
    (hτ₁ : Ty.Subtype τ₁ τ) (hτ₂ : Ty.Subtype τ₂ τ)
    (hu : u ≤ τ.outer) (hCap : Env.cap Γ₁ Γ₂ = some Γ₁₂)
    (hPlus : Env.plus Γ₀ Γ₁₂ = some Γ)
    (ih₀ : Valid Γ₀ ρ → V (.int u) (Substitution.apply ρ e₀))
    (ih₁ : Valid Γ₁ ρ → V τ₁ (Substitution.apply ρ e₁))
    (ih₂ : Valid Γ₂ ρ → V τ₂ (Substitution.apply ρ e₂))
    (hValid : Valid Γ ρ) :
    V τ (Substitution.apply ρ (.ite e₀ e₁ e₂)) := by
  have hValidPlus := valid_plus_split_of_semantic semantic_plus_V hPlus hValid
  have hValidBranches := valid_cap_split hCap hValidPlus.2
  have hV₀ := ih₀ hValidPlus.1
  have hV₁ := ih₁ hValidBranches.1
  have hV₂ := ih₂ hValidBranches.2
  simpa [Substitution.apply] using V_if hu hV₀ hV₁ hV₂ hτ₁ hτ₂

theorem fundamental_if_D
    {Γ Γ₀ Γ₁ Γ₂ Γ₁₂ : Env}
    {u : Usage} {τ₁ τ₂ τ : Ty} {e₀ e₁ e₂ : Term} {ρ : Substitution}
    (hτ₁ : Ty.Subtype τ₁ τ) (hτ₂ : Ty.Subtype τ₂ τ)
    (hu : u ≤ τ.outer) (hCap : Env.cap Γ₁ Γ₂ = some Γ₁₂)
    (hPlus : Env.plus Γ₀ Γ₁₂ = some Γ)
    (ih₀ : Valid Γ₀ ρ → V (.int u) (Substitution.apply ρ e₀))
    (ihD₀ : Valid Γ₀ ρ → SatisfiesD Γ₀ ρ →
      D (.int u) (Substitution.apply ρ e₀))
    (ih₁ : Valid Γ₁ ρ → V τ₁ (Substitution.apply ρ e₁))
    (ihD₁ : Valid Γ₁ ρ → SatisfiesD Γ₁ ρ →
      D τ₁ (Substitution.apply ρ e₁))
    (ih₂ : Valid Γ₂ ρ → V τ₂ (Substitution.apply ρ e₂))
    (ihD₂ : Valid Γ₂ ρ → SatisfiesD Γ₂ ρ →
      D τ₂ (Substitution.apply ρ e₂))
    (hValid : Valid Γ ρ) (hD : SatisfiesD Γ ρ) :
    D τ (Substitution.apply ρ (.ite e₀ e₁ e₂)) := by
  have hValidPlus := valid_plus_split_of_semantic semantic_plus_V hPlus hValid
  have hValidBranches := valid_cap_split hCap hValidPlus.2
  have hV₀ := ih₀ hValidPlus.1
  rcases satisfiesD_plus_split_of_semantic semantic_plus_D hPlus hD with hD₀ | hD₁₂
  · have hD₀' := ihD₀ hValidPlus.1 hD₀
    have hV₁ := ih₁ hValidBranches.1
    have hV₂ := ih₂ hValidBranches.2
    simpa [Substitution.apply] using
      D_if_from_condition hu hD₀' hV₁ hV₂ hτ₁ hτ₂
  · have hDBranches := satisfiesD_cap_split hCap hD₁₂
    have hD₁' := ihD₁ hValidBranches.1 hDBranches.1
    have hD₂' := ihD₂ hValidBranches.2 hDBranches.2
    simpa [Substitution.apply] using
      D_if_from_branches hu hV₀ hD₁' hD₂' hτ₁ hτ₂

/-- Simple typing of the substituted let, without an typing premise. -/
theorem let_applied_of_simpleTyping
    {Γ : Env} {τ : Ty} {e₁ e₂ : Term} {ρ : Substitution}
    (hSimple : Term.HasType (Env.erase Γ) (.letE e₁ e₂) τ.erase)
    (hValid : Valid Γ ρ) :
    Term.HasType []
      (.letE (Substitution.apply ρ e₁)
        (Substitution.applyAt ρ 1 e₂)) τ.erase := by
  have hImages : ∀ i σ, Term.lookup (Env.erase Γ) i = some σ →
      Term.HasType [] (ρ i) σ := by
    intro i σ hi
    exact (hValid.simpleValid_erased i σ hi).2
  have hApplied := Term.hasType_apply hSimple hImages
  simpa [Substitution.apply, Substitution.applyAt] using hApplied

theorem fundamental_let_V_of_simpleTyping
    {Γ Γ₁ Γ₂ : Env} {σ σ' τ : Ty}
    {e₁ e₂ : Term} {ρ : Substitution}
    (hSimple : Term.HasType (Env.erase Γ) (.letE e₁ e₂) τ.erase)
    (hSub : Ty.Subtype σ σ')
    (hPlus : Env.plus Γ₁ Γ₂ = some Γ)
    (ih₁ : Valid Γ₁ ρ → V σ (Substitution.apply ρ e₁))
    (ih₂ : ∀ {ρ : Substitution},
      Valid (σ' :: Γ₂) ρ → V τ (Substitution.apply ρ e₂))
    (hValid : Valid Γ ρ) :
    V τ (Substitution.apply ρ (.letE e₁ e₂)) := by
  have hValidSplit := valid_plus_split_of_semantic semantic_plus_V hPlus hValid
  have hDefV := ih₁ hValidSplit.1
  have hDefV' : V σ' (Substitution.apply ρ e₁) :=
    (semantic_subtype hSub).1 hDefV
  have hExtValid := valid_extend_head hDefV' hValidSplit.2
  have hBodyV := ih₂ hExtValid
  have hEq := Substitution.apply_extend_eq_instantiate_of_closed
    ρ (Substitution.apply ρ e₁) e₂ hValid.1 (V_closed hDefV)
  rw [hEq] at hBodyV
  have hContractAll := V_subset_allTerms τ hBodyV
  have hLetTyped := let_applied_of_simpleTyping hSimple hValid
  have hLetAll : AllTerms τ.erase
      (.letE (Substitution.apply ρ e₁) (Substitution.applyAt ρ 1 e₂)) :=
    ⟨Term.hasType_nil_closed hLetTyped, hLetTyped⟩
  have hEqSem := semEq_let hLetAll hContractAll
  exact (semantic_equiv_VD hEqSem).1.mpr hBodyV

theorem fundamental_let_D_of_simpleTyping
    {Γ Γ₁ Γ₂ : Env} {σ σ' τ : Ty}
    {e₁ e₂ : Term} {ρ : Substitution}
    (hSimple : Term.HasType (Env.erase Γ) (.letE e₁ e₂) τ.erase)
    (hSub : Ty.Subtype σ σ')
    (hPlus : Env.plus Γ₁ Γ₂ = some Γ)
    (ih₁ : Valid Γ₁ ρ → V σ (Substitution.apply ρ e₁))
    (ihD₁ : Valid Γ₁ ρ → SatisfiesD Γ₁ ρ →
      D σ (Substitution.apply ρ e₁))
    (ihD₂ : ∀ {ρ : Substitution},
      Valid (σ' :: Γ₂) ρ → SatisfiesD (σ' :: Γ₂) ρ →
        D τ (Substitution.apply ρ e₂))
    (hValid : Valid Γ ρ) (hD : SatisfiesD Γ ρ) :
    D τ (Substitution.apply ρ (.letE e₁ e₂)) := by
  have hValidSplit := valid_plus_split_of_semantic semantic_plus_V hPlus hValid
  have hDefV := ih₁ hValidSplit.1
  have hDefV' : V σ' (Substitution.apply ρ e₁) :=
    (semantic_subtype hSub).1 hDefV
  have hExtValidV := valid_extend_head hDefV' hValidSplit.2
  rcases satisfiesD_plus_split_of_semantic semantic_plus_D hPlus hD with hD₁ | hD₂
  · have hDefD := ihD₁ hValidSplit.1 hD₁
    have hDefD' : D σ' (Substitution.apply ρ e₁) :=
      (semantic_subtype hSub).2 hDefD
    have hDefDValid : V σ' (Substitution.apply ρ e₁) :=
      D_subset_V _ hDefD'
    have hExtValidD := valid_extend_head hDefDValid hValidSplit.2
    have hExtD := satisfiesD_extend_head (Γ := Γ₂) (ρ := ρ) hDefD'
    have hBodyD := ihD₂ hExtValidD hExtD
    have hEq := Substitution.apply_extend_eq_instantiate_of_closed
      ρ (Substitution.apply ρ e₁) e₂ hValid.1 (V_closed hDefV)
    rw [hEq] at hBodyD
    have hContractAll := D_subset_allTerms τ hBodyD
    have hLetTyped := let_applied_of_simpleTyping hSimple hValid
    have hLetAll : AllTerms τ.erase
        (.letE (Substitution.apply ρ e₁) (Substitution.applyAt ρ 1 e₂)) :=
      ⟨Term.hasType_nil_closed hLetTyped, hLetTyped⟩
    have hEqSem := semEq_let hLetAll hContractAll
    exact (semantic_equiv_VD hEqSem).2.mpr hBodyD
  · have hExtD := satisfiesD_extend_tail (σ := σ')
      (a := Substitution.apply ρ e₁) hD₂
    have hBodyD := ihD₂ hExtValidV hExtD
    have hEq := Substitution.apply_extend_eq_instantiate_of_closed
      ρ (Substitution.apply ρ e₁) e₂ hValid.1 (V_closed hDefV)
    rw [hEq] at hBodyD
    have hContractAll := D_subset_allTerms τ hBodyD
    have hLetTyped := let_applied_of_simpleTyping hSimple hValid
    have hLetAll : AllTerms τ.erase
        (.letE (Substitution.apply ρ e₁) (Substitution.applyAt ρ 1 e₂)) :=
      ⟨Term.hasType_nil_closed hLetTyped, hLetTyped⟩
    have hEqSem := semEq_let hLetAll hContractAll
    exact (semantic_equiv_VD hEqSem).2.mpr hBodyD


/-- T-Sub, V-side, using structural subtyping. -/
theorem fundamental_sub_V
    {Γ Γ' : Env} {τ τ' : Ty} {e : Term} {ρ : Substitution}
    (ihV : Valid Γ ρ → V τ (Substitution.apply ρ e))
    (hEnvSub : Env.Subtype Γ' Γ)
    (hTySub : Ty.Subtype τ τ')
    (hValid : Valid Γ' ρ) :
    V τ' (Substitution.apply ρ e) := by
  have hValidUp : Valid Γ ρ :=
    valid_of_env_subtype hEnvSub hValid
  exact (semantic_subtype hTySub).1 (ihV hValidUp)

/-- T-Sub, D-side, using structural subtyping. -/
theorem fundamental_sub_D
    {Γ Γ' : Env} {τ τ' : Ty} {e : Term} {ρ : Substitution}
    (ihD : Valid Γ ρ → SatisfiesD Γ ρ →
      D τ (Substitution.apply ρ e))
    (hEnvSub : Env.Subtype Γ' Γ)
    (hTySub : Ty.Subtype τ τ')
    (hValid : Valid Γ' ρ) (hD : SatisfiesD Γ' ρ) :
    D τ' (Substitution.apply ρ e) := by
  have hValidUp : Valid Γ ρ :=
    valid_of_env_subtype hEnvSub hValid
  have hDUp : SatisfiesD Γ ρ :=
    satisfiesD_of_env_subtype hEnvSub hD
  exact (semantic_subtype hTySub).2 (ihD hValidUp hDUp)

end Strictness
