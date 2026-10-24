import Strictness.Semantics.FixTypeOperations
import Strictness.Semantics.SemanticPlus
import Strictness.Semantics.SemanticPlusEnv

namespace Strictness

/-- The fix coefficient is top for an outer S/top annotation and L otherwise. -/
theorem fix_coefficient_cases (u : Usage) :
    (Usage.strict ≤ u ∧ Usage.scale u Usage.top = Usage.top) ∨
    (¬ Usage.strict ≤ u ∧ Usage.scale u Usage.top = Usage.lazy) := by
  cases u <;> simp [Usage.Le, Usage.scale]

namespace Ty

/-- The L-scaled copy of a type is a right unit for type addition. -/
theorem plus_lazy_scale_right (τ : Ty) :
    plus τ (scale Usage.lazy τ) = some τ := by
  induction τ with
  | int u =>
      cases u <;> rfl
  | prod σ τ u ihσ ihτ =>
      simp only [Ty.plus] at ihσ ihτ
      cases u <;>
        simp [Ty.plus, Ty.combine, Ty.scale, Usage.scale, Usage.add,
          ihσ, ihτ]
  | arrow σ τ u =>
      cases u <;>
        simp [Ty.plus, Ty.combine, Ty.scale, Usage.scale, Usage.add]

end Ty

namespace Env

/-- Composing an environment with its L-scaled copy leaves it unchanged. -/
theorem plus_lazy_scale_right (Γ : Env) :
    plus Γ (scale Usage.lazy Γ) = some Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      apply plus_cons_iff.mpr
      exact ⟨τ, Γ, Ty.plus_lazy_scale_right τ, ih, rfl⟩

end Env

/-- Without an outer S/top demand on the recursive variable, the fix
conclusion context is exactly the body context. -/
theorem fix_context_eq_of_not_strict
    {u : Usage} {Γ Δ : Env}
    (hu : ¬ Usage.strict ≤ u)
    (hPlus : Env.plus Γ (Env.scale (Usage.scale u Usage.top) Γ) = some Δ) :
    Δ = Γ := by
  have hCoeff : Usage.scale u Usage.top = Usage.lazy := by
    rcases fix_coefficient_cases u with ⟨hStrict, _⟩ | ⟨_, hLazy⟩
    · exact False.elim (hu hStrict)
    · exact hLazy
  rw [hCoeff, Env.plus_lazy_scale_right] at hPlus
  exact (Option.some.inj hPlus).symm

/-- Validity for the fix conclusion context supplies validity for the body
context, using the V-splitting theorem for addition. -/
theorem valid_of_fix_context
    {u : Usage} {Γ Δ : Env} {ρ : Substitution}
    (hPlus : Env.plus Γ (Env.scale (Usage.scale u Usage.top) Γ) = some Δ)
    (hValid : Valid Δ ρ) :
    Valid Γ ρ := by
  exact (valid_plus_split_of_semantic semantic_plus_V hPlus hValid).1

end Strictness
