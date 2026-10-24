import Strictness.Operational.SmallStepSubstitution
import Strictness.Operational.Properties

namespace Strictness

/-- The current evaluation position exposes an error marker. -/
def ErrorFocused (q : Term) : Prop :=
  ∃ E, q = EvalCtx.plug E .err

/-- Integer completion survives closing substitution and yields an
integer observation of the initial closed instance. -/
theorem steps_int_eval_of_closed_images
    {ρ : Substitution} (hρ : ∀ i, Term.Closed (ρ i))
    {e : Term} {n : Int} (hSteps : Steps e (.int n)) :
    Eval (Substitution.apply ρ e) (.int n) := by
  exact steps_eval (steps_apply_closed hρ hSteps) Eval.int

/-- An exposed error at the end of a finite prefix yields an error
observation of the initial closed instance. -/
theorem steps_errorFocused_evalErr_of_closed_images
    {ρ : Substitution} (hρ : ∀ i, Term.Closed (ρ i))
    {e q : Term} (hSteps : Steps e q) (hError : ErrorFocused q) :
    EvalErr (Substitution.apply ρ e) := by
  rcases hError with ⟨E, rfl⟩
  apply steps_evalErr (steps_apply_closed hρ hSteps)
  rw [EvalCtx.apply_plug]
  exact EvalCtx.plug_err_evalErr _

/-- Reaching a demanded variable yields an error observation after
replacing that variable by err. -/
theorem steps_demanded_err_evalErr
    {e q : Term} (hSteps : Steps e q) (hDemand : EvalCtx.Demanded q) :
    EvalErr (Substitution.apply (singleSubst .err) e) := by
  have hρ : ∀ i, Term.Closed (singleSubst .err i) := by
    intro i
    trivial
  exact steps_evalErr (steps_apply_closed hρ hSteps)
    (EvalCtx.demanded_err hDemand)


end Strictness
