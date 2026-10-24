import Strictness.Language.SimpleInstantiation
import Strictness.Operational.SmallStep

namespace Strictness

/-- Closing substitution preserves primitive CBN contractions.
The source terms may be open. -/
theorem rootStep_apply_closed
    {ρ : Substitution} (hρ : ∀ i, Term.Closed (ρ i))
    {r r' : Term} (h : RootStep r r') :
    RootStep (Substitution.apply ρ r) (Substitution.apply ρ r') := by
  cases h with
  | @beta body a =>
      rw [Substitution.apply_instantiate_of_closed_images ρ body a hρ]
      exact RootStep.beta
  | projLeft =>
      exact RootStep.projLeft
  | projRight =>
      exact RootStep.projRight
  | op o =>
      exact RootStep.op o
  | ifTrue hn =>
      exact RootStep.ifTrue hn
  | ifFalse =>
      exact RootStep.ifFalse
  | @letE e₁ e₂ =>
      rw [Substitution.apply_instantiate_of_closed_images ρ e₂ e₁ hρ]
      exact RootStep.letE
  | @fix body =>
      rw [Substitution.apply_instantiate_of_closed_images ρ body (.fix body) hρ]
      exact RootStep.fix
  | omega =>
      exact RootStep.omega

/-- Closing substitution preserves contextual CBN steps. -/
theorem step_apply_closed
    {ρ : Substitution} (hρ : ∀ i, Term.Closed (ρ i))
    {e e' : Term} (h : Step e e') :
    Step (Substitution.apply ρ e) (Substitution.apply ρ e') := by
  rcases h with ⟨E, r, r', hRoot, rfl, rfl⟩
  exact ⟨EvalCtx.map ρ E,
    Substitution.apply ρ r,
    Substitution.apply ρ r',
    rootStep_apply_closed hρ hRoot,
    EvalCtx.apply_plug ρ E r,
    EvalCtx.apply_plug ρ E r'⟩

/-- Closing substitution preserves every finite CBN reduction prefix,
including the zero-step prefix. -/
theorem steps_apply_closed
    {ρ : Substitution} (hρ : ∀ i, Term.Closed (ρ i))
    {e q : Term} (h : Steps e q) :
    Steps (Substitution.apply ρ e) (Substitution.apply ρ q) := by
  induction h with
  | refl =>
      exact Steps.refl
  | tail hSteps hStep ih =>
      exact Steps.tail ih (step_apply_closed hρ hStep)

end Strictness
