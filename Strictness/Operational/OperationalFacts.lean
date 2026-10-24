import Strictness.Operational.BigStep

namespace Strictness

namespace Term

@[simp] theorem eval_omega (v : Value) : ¬ Eval .omega v := by
  intro h
  cases h

@[simp] theorem evalErr_omega : ¬ EvalErr .omega := by
  intro h
  cases h

@[simp] theorem not_diverges_of_err : ¬ Diverges .err := by
  intro h
  exact h.2 EvalErr.err

@[simp] theorem omega_diverges : Diverges .omega := by
  constructor
  · intro h
    rcases h with ⟨v, hv⟩
    exact eval_omega v hv
  · intro h
    exact evalErr_omega h

@[simp] theorem closed_omega : Closed .omega := by
  trivial

@[simp] theorem closed_err : Closed .err := by
  trivial

end Term

end Strictness
