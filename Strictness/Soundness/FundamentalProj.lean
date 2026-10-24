import Strictness.Semantics.SemanticPairProjection
import Strictness.Semantics.SemanticSubstitution

namespace Strictness

open Term

/-- T-Proj left V-case. -/
theorem fundamental_proj_left_V
    {Γ : Env} {σ τ : Ty} {u : Usage} {e : Term} {ρ : Substitution}
    (hu : u ≤ σ.outer)
    (hLazy : Ty.IsLazy τ)
    (ihV : Valid Γ ρ → V (.prod σ τ u) (Substitution.apply ρ e))
    (hValid : Valid Γ ρ) :
    V σ (Substitution.apply ρ (.proj true e)) := by
  simpa [Substitution.apply] using
    (V_proj_left hu hLazy (ihV hValid))

/-- T-Proj right V case. -/
theorem fundamental_proj_right_V
    {Γ : Env} {σ τ : Ty} {u : Usage} {e : Term} {ρ : Substitution}
    (hu : u ≤ τ.outer)
    (hLazy : Ty.IsLazy σ)
    (ihV : Valid Γ ρ → V (.prod σ τ u) (Substitution.apply ρ e))
    (hValid : Valid Γ ρ) :
    V τ (Substitution.apply ρ (.proj false e)) := by
  simpa [Substitution.apply] using
    (V_proj_right hu hLazy (ihV hValid))

/-- T-Proj left D-case. -/
theorem fundamental_proj_left_D
    {Γ : Env} {σ τ : Ty} {u : Usage} {e : Term} {ρ : Substitution}
    (hu : u ≤ σ.outer)
    (hLazy : Ty.IsLazy τ)
    (_ : Valid Γ ρ → V (.prod σ τ u) (Substitution.apply ρ e))
    (ihD : Valid Γ ρ → SatisfiesD Γ ρ → D (.prod σ τ u) (Substitution.apply ρ e))
    (hValid : Valid Γ ρ)
    (hD : SatisfiesD Γ ρ) :
    D σ (Substitution.apply ρ (.proj true e)) := by
  simpa [Substitution.apply] using
    (D_proj_left hu hLazy (ihD hValid hD))

/-- T-Proj right D case. -/
theorem fundamental_proj_right_D
    {Γ : Env} {σ τ : Ty} {u : Usage} {e : Term} {ρ : Substitution}
    (hu : u ≤ τ.outer)
    (hLazy : Ty.IsLazy σ)
    (_ : Valid Γ ρ → V (.prod σ τ u) (Substitution.apply ρ e))
    (ihD : Valid Γ ρ → SatisfiesD Γ ρ → D (.prod σ τ u) (Substitution.apply ρ e))
    (hValid : Valid Γ ρ)
    (hD : SatisfiesD Γ ρ) :
    D τ (Substitution.apply ρ (.proj false e)) := by
  simpa [Substitution.apply] using
    (D_proj_right hu hLazy (ihD hValid hD))

end Strictness
