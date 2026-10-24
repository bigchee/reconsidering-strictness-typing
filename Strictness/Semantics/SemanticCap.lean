import Strictness.Semantics.SemanticSubtype
import Strictness.Semantics.SemanticEnvironment
import Strictness.Semantics.EnvironmentLemmas

namespace Strictness

open Term

/-- Meet combination on types is semantically contained in both operands.  This is an immediate consequence of the two subtype projections
of the meet and the semantic soundness of subtyping. -/
theorem semantic_cap {σ τ ρ : Ty} (h : Ty.cap σ τ = some ρ) :
    TermSet.Subset (V ρ) (V σ) ∧
    TermSet.Subset (V ρ) (V τ) ∧
    TermSet.Subset (D ρ) (D σ) ∧
    TermSet.Subset (D ρ) (D τ) := by
  rcases semantic_subtype (cap_subtype_left h) with ⟨hVL, hDL⟩
  rcases semantic_subtype (cap_subtype_right h) with ⟨hVR, hDR⟩
  exact ⟨hVL, hVR, hDL, hDR⟩

/-- An environment meet therefore makes a V-valid substitution valid for both
branch environments. -/
theorem valid_cap_split {Γ₁ Γ₂ Γ : Env} {ρ : Substitution}
    (hcap : Env.cap Γ₁ Γ₂ = some Γ) (hvalid : Valid Γ ρ) :
    Valid Γ₁ ρ ∧ Valid Γ₂ ρ := by
  have hlen := Env.cap_some_length hcap
  constructor
  · refine ⟨hvalid.1, ?_⟩
    intro i σ hσ
    obtain ⟨τ, hτ⟩ := Env.lookup_exists_of_same_length hlen hσ
    rcases Env.cap_lookup_of_inputs hcap hσ hτ with ⟨υ, hυ, hcapTy⟩
    rcases semantic_cap hcapTy with ⟨hV₁, hV₂, _, _⟩
    exact hV₁ (hvalid.2 i υ hυ)
  · refine ⟨hvalid.1, ?_⟩
    intro i τ hτ
    obtain ⟨σ, hσ⟩ := Env.lookup_exists_of_same_length hlen.symm hτ
    rcases Env.cap_lookup_of_inputs hcap hσ hτ with ⟨υ, hυ, hcapTy⟩
    rcases semantic_cap hcapTy with ⟨_, hV₂, _, _⟩
    exact hV₂ (hvalid.2 i υ hυ)

/-- A D-witness in a meet-combined environment can be transported to both
branch environments. -/
theorem satisfiesD_cap_split {Γ₁ Γ₂ Γ : Env} {ρ : Substitution}
    (hcap : Env.cap Γ₁ Γ₂ = some Γ) (hD : SatisfiesD Γ ρ) :
    SatisfiesD Γ₁ ρ ∧ SatisfiesD Γ₂ ρ := by
  rcases hD with ⟨i, υ, hυ, hDυ⟩
  rcases (Env.cap_lookup_iff hcap).mp hυ with ⟨σ, τ, hσ, hτ, hcapTy⟩
  rcases semantic_cap hcapTy with ⟨_, _, hD₁, hD₂⟩
  exact ⟨⟨i, σ, hσ, hD₁ hDυ⟩, ⟨i, τ, hτ, hD₂ hDυ⟩⟩

end Strictness
