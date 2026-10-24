import Strictness.Operational.Progress
import Strictness.Soundness.FiniteObservations

namespace Strictness

/-- Strict case: every terminal state reached by open-term CBN
reduction directly demands the single free variable.
This theorem does not assert that a terminal state is reached. -/
theorem strict_smallStep_terminal_demands
    {σ : Ty} {e q : Term}
    (hTyping :
      Typing [σ.reannotate Usage.strict] e (.int Usage.strict))
    (hSteps : Steps e q)
    (hTerminal : SmallStepTerminal q) :
    EvalCtx.Demanded q := by
  have hErased : Term.HasType [σ.erase] e .int := by
    simpa using typing_erasure hTyping
  have hQ : Term.HasType [σ.erase] q .int :=
    steps_hasType_open hSteps hErased
  rcases typed_open_int_terminal_forms hQ hTerminal with
    hDemand | hError | ⟨n, rfl⟩
  · exact hDemand
  · exact False.elim
      (strict_smallStep_no_errorFocused hTyping hSteps hError)
  · exact False.elim
      (strict_smallStep_no_int hTyping n hSteps)

/-- Top case: every state reached from the original open term
admits a further source-language step. -/
theorem top_reachable_can_step
    {σ : Ty} {e q : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict))
    (hSteps : Steps e q) :
    ∃ q', Step q q' := by
  have hErased : Term.HasType [σ.erase] e .int := by
    simpa using typing_erasure hTyping
  have hQ : Term.HasType [σ.erase] q .int :=
    steps_hasType_open hSteps hErased
  rcases typed_progress_open hQ with
    hStep | hVal | hVar | hError
  · exact hStep
  · cases hVal with
    | int n =>
        exact False.elim
          (top_smallStep_no_int hTyping n hSteps)
    | lam body => cases hQ
    | pair e₁ e₂ => cases hQ
  · exact False.elim
      (top_smallStep_no_demand hTyping hSteps
        (variableFocused_singleton_demands hVar))
  · exact False.elim
      (top_smallStep_no_errorFocused hTyping hSteps hError)

/-- Top case: the original open term itself has an infinite
CBN source reduction sequence. The initial term is open; no error substitution is performed. -/
theorem top_open_infiniteSteps
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    InfiniteSteps e := by
  apply infiniteSteps_of_reachable_can_step
  intro q hSteps
  exact top_reachable_can_step hTyping hSteps

/-- Top case: infinite execution of the original open term,
with demand and integer completion excluded along every finite prefix. -/
theorem top_open_smallStep
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    InfiniteSteps e ∧
    (∀ {q}, Steps e q → ¬ EvalCtx.Demanded q) ∧
    (∀ n, ¬ Steps e (.int n)) := by
  exact ⟨top_open_infiniteSteps hTyping,
    top_smallStep_no_demand hTyping,
    top_smallStep_no_int hTyping⟩

/-- In the S case, a reached state is terminal exactly when it demands
the single free variable. Reaching a terminal state is not asserted. -/
theorem strict_smallStep_terminal_iff_demands
    {σ : Ty} {e q : Term}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict))
    (hSteps : Steps e q) :
    SmallStepTerminal q ↔ EvalCtx.Demanded q := by
  exact ⟨strict_smallStep_terminal_demands hTyping hSteps,
    demanded_smallStep_terminal⟩

end Strictness
