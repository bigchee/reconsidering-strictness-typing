import Strictness.Semantics.SemanticApplication
import Strictness.Semantics.SemanticPlusEnv
import Strictness.Semantics.SemanticSubstitution
import Strictness.Semantics.SemanticSubtype
import Strictness.Language.Erasure

namespace Strictness

open Usage
open Term

/-- T-App V-case: the split environment supplies the induction hypotheses
for the semantic application lemma. -/
theorem fundamental_app_V_of_simpleTyping
    {Γ₁ Γ₂ : Env} {σ σ' τ : Ty} {u : Usage}
    {e₁ e₂ : Term} {ρ : Substitution}
    (hArgSimple : Term.HasType (Env.erase Γ₂) e₂ σ'.erase)
    (hSub : Ty.Subtype σ' σ)
    (hu : u ≤ τ.outer)
    (ihV₁ : Valid Γ₁ ρ →
      V (.arrow σ τ u) (Substitution.apply ρ e₁))
    (ihV₂ : Valid Γ₂ ρ →
      V σ' (Substitution.apply ρ e₂))
    (hValid₁ : Valid Γ₁ ρ)
    (hValid₂ : Valid (Env.scale u Γ₂) ρ) :
    V τ (Substitution.apply ρ (.app e₁ e₂)) := by
  have hF := ihV₁ hValid₁
  cases u with
  | unknown =>
      have hA : V σ (Substitution.apply ρ e₂) :=
        (semantic_subtype hSub).1 (ihV₂ (valid_of_unknown_scale hValid₂))
      simpa [Substitution.apply] using V_arrow_apply hu hF hA
  | strict =>
      have hA : V σ (Substitution.apply ρ e₂) :=
        (semantic_subtype hSub).1 (ihV₂ (valid_of_strict_scale hValid₂))
      simpa [Substitution.apply] using V_arrow_apply hu hF hA
  | lazy =>
      have hImages : ∀ i α, Term.lookup (Env.erase Γ₂) i = some α →
          AllTerms α (ρ i) := by
        simpa only [Env.erase_scale] using hValid₂.simpleValid_erased
      have hArgType := Term.hasType_apply hArgSimple
        (fun i α h => (hImages i α h).2)
      have hArgAll : AllTerms σ'.erase (Substitution.apply ρ e₂) :=
        ⟨Term.hasType_nil_closed hArgType, hArgType⟩
      have hArgAllσ : AllTerms σ.erase (Substitution.apply ρ e₂) := by
        simpa only [Ty.subtype_erase hSub] using hArgAll
      have hAppAll := allTerms_app
        (V_subset_allTerms (.arrow σ τ lazy) hF) hArgAllσ
      have hOuter : τ.outer = lazy ∨ τ.outer = top :=
        Usage.le_lazy_iff.mp hu
      rcases hOuter with hOuter | hOuter
      · rw [V_eq_allTerms_of_outer_lazy hOuter]
        simpa [Substitution.apply] using hAppAll
      · rw [V_eq_allTerms_of_outer_top hOuter]
        simpa [Substitution.apply] using hAppAll
  | top =>
      have hImages : ∀ i α, Term.lookup (Env.erase Γ₂) i = some α →
          AllTerms α (ρ i) := by
        simpa only [Env.erase_scale] using hValid₂.simpleValid_erased
      have hArgType := Term.hasType_apply hArgSimple
        (fun i α h => (hImages i α h).2)
      have hArgAll : AllTerms σ'.erase (Substitution.apply ρ e₂) :=
        ⟨Term.hasType_nil_closed hArgType, hArgType⟩
      have hArgAllσ : AllTerms σ.erase (Substitution.apply ρ e₂) := by
        simpa only [Ty.subtype_erase hSub] using hArgAll
      have hAppAll := allTerms_app
        (V_subset_allTerms (.arrow σ τ top) hF) hArgAllσ
      have hOuter : τ.outer = top := Usage.le_top_iff.mp hu
      rw [V_eq_allTerms_of_outer_top hOuter]
      simpa [Substitution.apply] using hAppAll

/-- T-App D-case. The additional split is whether the
combined D-witness belongs to the function side or the argument side. -/
theorem fundamental_app_D_of_simpleTyping
    {Γ₁ Γ₂ : Env} {σ σ' τ : Ty} {u : Usage}
    {e₁ e₂ : Term} {ρ : Substitution}
    (hArgSimple : Term.HasType (Env.erase Γ₂) e₂ σ'.erase)
    (hSub : Ty.Subtype σ' σ)
    (hu : u ≤ τ.outer)
    (ihV₁ : Valid Γ₁ ρ →
      V (.arrow σ τ u) (Substitution.apply ρ e₁))
    (ihD₁ : Valid Γ₁ ρ → SatisfiesD Γ₁ ρ →
      D (.arrow σ τ u) (Substitution.apply ρ e₁))
    (ihV₂ : Valid Γ₂ ρ →
      V σ' (Substitution.apply ρ e₂))
    (ihD₂ : Valid Γ₂ ρ → SatisfiesD Γ₂ ρ →
      D σ' (Substitution.apply ρ e₂))
    (hValid₁ : Valid Γ₁ ρ)
    (hValid₂ : Valid (Env.scale u Γ₂) ρ)
    (hDsplit : SatisfiesD Γ₁ ρ ∨
      SatisfiesD (Env.scale u Γ₂) ρ) :
    D τ (Substitution.apply ρ (.app e₁ e₂)) := by
  cases u with
  | unknown =>
      rcases hDsplit with hD₁ | hD₂
      · have hDF := ihD₁ hValid₁ hD₁
        rw [D_arrow_unknown_eq_empty] at hDF
        exact False.elim hDF
      · exact False.elim
          ((not_satisfiesD_of_lazy (Env.isLazy_unknown_scale Γ₂)) hD₂)
  | strict =>
      have hValid₂' := valid_of_strict_scale hValid₂
      have hF := ihV₁ hValid₁
      have hA : V σ (Substitution.apply ρ e₂) :=
        (semantic_subtype hSub).1 (ihV₂ hValid₂')
      rcases hDsplit with hD₁ | hD₂
      · simpa [Substitution.apply] using D_arrow_apply hu (ihD₁ hValid₁ hD₁) hA
      · have hD₂' : SatisfiesD Γ₂ ρ := by simpa only [Env.strict_scale] using hD₂
        have hA_D : D σ (Substitution.apply ρ e₂) :=
          (semantic_subtype hSub).2 (ihD₂ hValid₂' hD₂')
        simpa [Substitution.apply] using
          V_arrow_apply_D hu (Or.inl rfl) hF hA_D
  | lazy =>
      rcases hDsplit with hD₁ | hD₂
      · have hLazy : Ty.IsLazy (.arrow σ τ lazy) := by trivial
        have hDF := ihD₁ hValid₁ hD₁
        rw [lazy_implies_D_empty hLazy] at hDF
        exact False.elim hDF
      · exact False.elim
          ((not_satisfiesD_of_lazy (Env.isLazy_lazy_scale Γ₂)) hD₂)
  | top =>
      have hImages : ∀ i α, Term.lookup (Env.erase Γ₂) i = some α →
          AllTerms α (ρ i) := by
        simpa only [Env.erase_scale] using hValid₂.simpleValid_erased
      have hArgType := Term.hasType_apply hArgSimple
        (fun i α h => (hImages i α h).2)
      have hArgAll : AllTerms σ'.erase (Substitution.apply ρ e₂) :=
        ⟨Term.hasType_nil_closed hArgType, hArgType⟩
      have hArgAllσ : AllTerms σ.erase (Substitution.apply ρ e₂) := by
        simpa only [Ty.subtype_erase hSub] using hArgAll
      have hAppAll := allTerms_app
        (V_subset_allTerms (.arrow σ τ top) (ihV₁ hValid₁)) hArgAllσ
      have hOuter : τ.outer = top := Usage.le_top_iff.mp hu
      rw [D_eq_allTerms_of_outer_top hOuter]
      simpa [Substitution.apply] using hAppAll

end Strictness
