import Strictness.Semantics.SemanticSubtype
import Strictness.Semantics.SemanticEnvironment
import Strictness.Semantics.EnvironmentLemmas

namespace Strictness

open Term

/-- Environment-level V splitting from semantic containment for type addition.
The type-level containment theorem is an explicit parameter of this bridge. -/
theorem valid_plus_split_of_semantic
    (hPlusSem : ∀ {σ τ ρ : Ty}, Ty.plus σ τ = some ρ →
      TermSet.Subset (V ρ) (V σ) ∧ TermSet.Subset (V ρ) (V τ))
    {Γ₁ Γ₂ Γ : Env} {ρ : Substitution}
    (hplus : Env.plus Γ₁ Γ₂ = some Γ) (hvalid : Valid Γ ρ) :
    Valid Γ₁ ρ ∧ Valid Γ₂ ρ := by
  have hlen := Env.plus_some_length hplus
  constructor
  · refine ⟨hvalid.1, ?_⟩
    intro i σ hσ
    obtain ⟨τ, hτ⟩ := Env.lookup_exists_of_same_length hlen hσ
    rcases Env.plus_lookup_of_inputs hplus hσ hτ with ⟨υ, hυ, hty⟩
    exact (hPlusSem hty).1 (hvalid.2 i υ hυ)
  · refine ⟨hvalid.1, ?_⟩
    intro i τ hτ
    obtain ⟨σ, hσ⟩ := Env.lookup_exists_of_same_length hlen.symm hτ
    rcases Env.plus_lookup_of_inputs hplus hσ hτ with ⟨υ, hυ, hty⟩
    exact (hPlusSem hty).2 (hvalid.2 i υ hυ)

/-- Environment-level D splitting from semantic containment for type addition.
A D-witness of the combined environment becomes a witness on at least one
of the two component environments. -/
theorem satisfiesD_plus_split_of_semantic
    (hPlusSem : ∀ {σ τ ρ : Ty}, Ty.plus σ τ = some ρ →
      TermSet.Subset (D ρ) (TermSet.union (D σ) (D τ)))
    {Γ₁ Γ₂ Γ : Env} {ρ : Substitution}
    (hplus : Env.plus Γ₁ Γ₂ = some Γ) (hD : SatisfiesD Γ ρ) :
    SatisfiesD Γ₁ ρ ∨ SatisfiesD Γ₂ ρ := by
  rcases hD with ⟨i, υ, hυ, hDυ⟩
  rcases (Env.plus_lookup_iff hplus).mp hυ with
    ⟨σ, τ, hσ, hτ, hty⟩
  have hUnion := hPlusSem hty hDυ
  rcases hUnion with hσD | hτD
  · exact Or.inl ⟨i, σ, hσ, hσD⟩
  · exact Or.inr ⟨i, τ, hτ, hτD⟩

end Strictness
