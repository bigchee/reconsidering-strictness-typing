import Strictness.Semantics.SemanticPairProjection
import Strictness.Semantics.SemanticPlusEnv
import Strictness.Semantics.SemanticSubstitution

namespace Strictness

open Usage
open Term

/-- T-Pair V-case. It needs the two V-induction hypotheses;
the typing side conditions are carried by the pair rule itself. -/
theorem fundamental_pair_V
    {Γ₁ Γ₂ : Env} {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    {ρ : Substitution}
    (ihV₁ : Valid Γ₁ ρ → V σ (Substitution.apply ρ e₁))
    (ihV₂ : Valid Γ₂ ρ → V τ (Substitution.apply ρ e₂))
    (hValid₁ : Valid Γ₁ ρ)
    (hValid₂ : Valid Γ₂ ρ)
    : V (.prod σ τ u) (Substitution.apply ρ (.pair e₁ e₂)) := by
  have hV₁ := ihV₁ hValid₁
  have hV₂ := ihV₂ hValid₂
  simpa [Substitution.apply] using (V_pair_intro hV₁ hV₂)

/-- T-Pair D-case, with the environment's D-witness already split between
the two component environments. -/
theorem fundamental_pair_D
    {Γ₁ Γ₂ : Env} {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    (hσOuter : σ.outer ≤ u ⊔ lazy)
    (hτOuter : τ.outer ≤ u ⊔ lazy)
    {ρ : Substitution}
    (ihV₁ : Valid Γ₁ ρ → V σ (Substitution.apply ρ e₁))
    (ihD₁ : Valid Γ₁ ρ → SatisfiesD Γ₁ ρ → D σ (Substitution.apply ρ e₁))
    (ihV₂ : Valid Γ₂ ρ → V τ (Substitution.apply ρ e₂))
    (ihD₂ : Valid Γ₂ ρ → SatisfiesD Γ₂ ρ → D τ (Substitution.apply ρ e₂))
    (hValid₁ : Valid Γ₁ ρ)
    (hValid₂ : Valid Γ₂ ρ)
    (hDsplit : SatisfiesD Γ₁ ρ ∨ SatisfiesD Γ₂ ρ) :
    D (.prod σ τ u) (Substitution.apply ρ (.pair e₁ e₂)) := by
  have hV₁ := ihV₁ hValid₁
  have hV₂ := ihV₂ hValid₂
  rcases hDsplit with hD₁ | hD₂
  · have hD₁' := ihD₁ hValid₁ hD₁
    simpa [Substitution.apply] using
      (D_pair_left_intro hD₁' hV₂ hσOuter hτOuter)
  · have hD₂' := ihD₂ hValid₂ hD₂
    simpa [Substitution.apply] using
      (D_pair_right_intro hV₁ hD₂' hσOuter hτOuter)

end Strictness
