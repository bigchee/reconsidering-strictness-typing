import Strictness.Operational.Observations
import Strictness.Operational.Machine.Consequences
import Strictness.Soundness.Semantic

namespace Strictness

/-- Lazy case: no finite open-term reduction prefix demands the
single free variable. -/
theorem lazy_smallStep
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.lazy] e (.int Usage.strict)) :
    ∀ {q}, Steps e q → ¬ EvalCtx.Demanded q := by
  intro q hSteps hDemand
  exact lazy_no_error hTyping
    (steps_demanded_err_evalErr hSteps hDemand)

/-- Strict case: integer completion is impossible. -/
theorem strict_smallStep_no_int
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict)) :
    ∀ n, ¬ Steps e (.int n) := by
  intro n hSteps
  have hDiv := strict_semantic hTyping
    (omega_mem_D_reannotate_strict σ)
  have hρ : ∀ i, Term.Closed (singleSubst .omega i) := by
    intro i
    trivial
  exact hDiv.1 ⟨.int n, steps_int_eval_of_closed_images hρ hSteps⟩

/-- Strict case: no finite prefix exposes an error marker. -/
theorem strict_smallStep_no_errorFocused
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict)) :
    ∀ {q}, Steps e q → ¬ ErrorFocused q := by
  intro q hSteps hError
  have hDiv := strict_semantic hTyping
    (omega_mem_D_reannotate_strict σ)
  have hρ : ∀ i, Term.Closed (singleSubst .omega i) := by
    intro i
    trivial
  exact hDiv.2 (steps_errorFocused_evalErr_of_closed_images hρ hSteps hError)

/-- Top case: no finite prefix demands the single free variable. -/
theorem top_smallStep_no_demand
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    ∀ {q}, Steps e q → ¬ EvalCtx.Demanded q := by
  intro q hSteps hDemand
  exact (top_semantic hTyping).2
    (steps_demanded_err_evalErr hSteps hDemand)

/-- Top case: integer completion is impossible. -/
theorem top_smallStep_no_int
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    ∀ n, ¬ Steps e (.int n) := by
  intro n hSteps
  have hρ : ∀ i, Term.Closed (singleSubst .err i) := by
    intro i
    trivial
  exact (top_semantic hTyping).1
    ⟨.int n, steps_int_eval_of_closed_images hρ hSteps⟩

/-- Top case: no finite prefix exposes an error marker. -/
theorem top_smallStep_no_errorFocused
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    ∀ {q}, Steps e q → ¬ ErrorFocused q := by
  intro q hSteps hError
  have hρ : ∀ i, Term.Closed (singleSubst .err i) := by
    intro i
    trivial
  exact (top_semantic hTyping).2
    (steps_errorFocused_evalErr_of_closed_images hρ hSteps hError)

/-- Finite-prefix observations of the open term and infinite reduction of
its error instance. `top_open_smallStep` additionally establishes
infinite source reduction of the open term itself. -/
theorem top_smallStep
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    InfiniteSteps (Substitution.apply (singleSubst .err) e) ∧
    (∀ {q}, Steps e q → ¬ EvalCtx.Demanded q) ∧
    (∀ n, ¬ Steps e (.int n)) := by
  exact ⟨top_infinite_steps hTyping,
    top_smallStep_no_demand hTyping,
    top_smallStep_no_int hTyping⟩

end Strictness
