import Strictness.Operational.Machine.Substitution
import Strictness.Soundness.Semantic

/-!
Semantic soundness consequences for the closure machine.

Combines the semantic substitution consequences of the fundamental lemma
with machine readback and replacement simulation. This is the machine layer
that depends on the semantic soundness argument; the preceding machine
modules establish general operational properties.
-/

namespace Strictness

/-- Auxiliary lemma for the L main result.  No finite prefix of the open
machine can demand the single free variable: such a demand would make the
`err` instantiation evaluate to the observable error marker. -/
theorem lazy_no_machine_demand {σ : Ty} {e : Term} {s : MachineState}
    (hTyping : Typing [σ.reannotate Usage.lazy] e (.int Usage.strict))
    (hSteps : MachineSteps (MachineState.open1 e) s) :
    ¬ MachineState.Demands s := by
  intro hDemand
  rcases demand_reaches_err_machine hSteps hDemand with ⟨sErr, hErrSteps, hErr⟩
  have hClosedErr : Term.Closed (.err : Term) := trivial
  have hEvalErr := machine_error_implies_evalErr hClosedErr hErrSteps hErr
  exact lazy_no_error hTyping hEvalErr

/-- Machine-level lazy observation: An L-annotated variable is never
demanded in any finite prefix of the open CBN machine. -/
theorem lazy_operational {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.lazy] e (.int Usage.strict)) :
    ∀ {s}, MachineSteps (MachineState.open1 e) s → ¬ MachineState.Demands s := by
  intro s hSteps
  exact lazy_no_machine_demand hTyping hSteps

/-- Auxiliary lemma for the S main result: replacing the source variable by
`omega` rules out every completed integer observation of the open machine. -/
theorem strict_no_machine_return_int {σ : Ty} {e : Term}
    {s : MachineState} {n : Int}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict))
    (hSteps : MachineSteps (MachineState.open1 e) s)
    (hReturn : MachineState.ReturnsInt s n) : False := by
  have hClosedOmega : Term.Closed (.omega : Term) := trivial
  rcases open_steps_replaced (a := .omega) hSteps with ⟨sOmega, hOmegaSteps, hRel⟩
  have hOmegaReturn := replace_returnsInt hRel hReturn
  have hEval := machine_return_int_implies_eval hClosedOmega hOmegaSteps hOmegaReturn
  have hDiverges := strict_semantic hTyping
    (omega_mem_D_reannotate_strict σ)
  exact hDiverges.1 ⟨.int n, hEval⟩

/-- Auxiliary lemma for the S main result: the `omega` instantiation of an
S-typed term cannot expose the semantic error marker either. -/
theorem strict_no_machine_error {σ : Ty} {e : Term}
    {s : MachineState}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict))
    (hSteps : MachineSteps (MachineState.open1 e) s)
    (hError : MachineState.IsError s) : False := by
  have hClosedOmega : Term.Closed (.omega : Term) := trivial
  rcases open_steps_replaced (a := .omega) hSteps with ⟨sOmega, hOmegaSteps, hRel⟩
  have hOmegaError := replace_error hRel hError
  have hEvalErr := machine_error_implies_evalErr hClosedOmega hOmegaSteps hOmegaError
  exact (strict_semantic hTyping
    (omega_mem_D_reannotate_strict σ)).2 hEvalErr

/-- Machine-level strict observation: For an `Int^S` result, every finite
machine terminal is exactly a demand for the sole open variable, i.e. the
paper's `E[x]` form. -/
theorem strict_terminal_demands {σ : Ty} {e : Term} {s : MachineState}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict))
    (hSteps : MachineSteps (MachineState.open1 e) s)
    (hTerminal : MachineState.Terminal s) : MachineState.Demands s := by
  have hErased : Term.HasType [σ.erase] e .int := by
    simpa using typing_erasure hTyping
  have hTyped : TypedState s .int :=
    typed_machine_steps (initial_typed_state hErased) hSteps
  rcases typed_terminal_forms hTyped hTerminal with hDemand | hError | ⟨n, hReturn⟩
  · exact hDemand
  · exact False.elim (strict_no_machine_error hTyping hSteps hError)
  · exact False.elim (strict_no_machine_return_int hTyping hSteps hReturn)

/-- Derived S corollary, retained for callers interested only in completed
integer observations.  The stronger machine-terminal statement is
`strict_terminal_demands` above. -/
theorem strict_operational {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.strict] e (.int Usage.strict)) :
    ∀ {s n}, MachineSteps (MachineState.open1 e) s →
      MachineState.ReturnsInt s n → False := by
  intro s n hSteps hReturn
  exact strict_no_machine_return_int hTyping hSteps hReturn

/-- Auxiliary lemma for the ⊤ main result: ⊤ cannot expose a demand in any
finite open-machine prefix. -/
theorem top_no_machine_demand {σ : Ty} {e : Term} {s : MachineState}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict))
    (hSteps : MachineSteps (MachineState.open1 e) s) :
    ¬ MachineState.Demands s := by
  intro hDemand
  rcases demand_reaches_err_machine hSteps hDemand with ⟨sErr, hErrSteps, hErr⟩
  have hEvalErr := machine_error_implies_evalErr (a := .err) (by trivial) hErrSteps hErr
  exact (top_semantic hTyping).2 hEvalErr

/-- Auxiliary lemma for the ⊤ main result: ⊤ cannot expose a completed
integer observation in a finite open-machine prefix. -/
theorem top_no_machine_return_int {σ : Ty} {e : Term}
    {s : MachineState} {n : Int}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict))
    (hSteps : MachineSteps (MachineState.open1 e) s)
    (hReturn : MachineState.ReturnsInt s n) : False := by
  rcases open_steps_replaced (a := .err) hSteps with ⟨sErr, hErrSteps, hRel⟩
  have hErrReturn := replace_returnsInt hRel hReturn
  have hEval := machine_return_int_implies_eval (a := .err) (by trivial)
    hErrSteps hErrReturn
  exact (top_semantic hTyping).1 ⟨.int n, hEval⟩

/-- Auxiliary lemma for the ⊤ main result: the divergent `err` instantiation
has a genuine infinite CBN source reduction trace. -/
theorem top_infinite_steps {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    InfiniteSteps (Substitution.apply (singleSubst .err) e) := by
  have hErased : Term.HasType [σ.erase] e .int := by
    simpa using typing_erasure hTyping
  have hTypedErr : Term.HasType [] (Substitution.apply (singleSubst .err) e) .int :=
    Term.hasType_apply hErased (by
      intro i τ hLookup
      cases i with
      | zero =>
        simp only [Term.lookup] at hLookup
        cases hLookup
        exact Term.HasType.err
      | succ i => simp [Term.lookup] at hLookup)
  exact goodDivergingInt_infiniteSteps ⟨hTypedErr, top_semantic hTyping⟩

/-- Machine-level top observation: The `err` instantiation has an infinite
CBN trace, while no finite open-machine prefix demands the variable or
produces a completed integer. -/
theorem top_operational {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate Usage.top] e (.int Usage.strict)) :
    InfiniteSteps (Substitution.apply (singleSubst .err) e) ∧
    (∀ {s}, MachineSteps (MachineState.open1 e) s → ¬ MachineState.Demands s) ∧
    (∀ {s n}, MachineSteps (MachineState.open1 e) s →
      MachineState.ReturnsInt s n → False) := by
  exact ⟨top_infinite_steps hTyping,
    (by intro s hSteps; exact top_no_machine_demand hTyping hSteps),
    (by intro s n hSteps hReturn
        exact top_no_machine_return_int hTyping hSteps hReturn)⟩

end Strictness
