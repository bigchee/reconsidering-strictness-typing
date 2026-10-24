import Strictness.Operational.OperationalLemmas
import Strictness.Soundness.FiniteObservations

/-!
Concrete evaluation checks for conditionals, arithmetic and error demand.

Checks operand order, nonzero truth, and evaluation of both operands even
when an arithmetic identity might otherwise suggest a shortcut.
-/

namespace Strictness

/-- The arithmetic result is the interpretation of the preserved operator. -/
example (o : PrimOp) (n₁ n₂ : Int) :
    Eval (.op o (.int n₁) (.int n₂)) (.int (o.eval n₁ n₂)) :=
  Eval.op o Eval.int Eval.int

/-- Subtraction checks the order of the operands. -/
example : Eval (.op .sub (.int 8) (.int 3)) (.int 5) :=
  Eval.op .sub Eval.int Eval.int

example : Eval (.op .mul (.int (-3)) (.int 4)) (.int (-12)) :=
  Eval.op .mul Eval.int Eval.int

example : RootStep (.op .sub (.int 8) (.int 3)) (.int 5) :=
  RootStep.op .sub

/-- Multiplication evaluates its second operand even when the first is zero. -/
example : EvalErr (.op .mul (.int 0) .err) :=
  EvalErr.opRight .mul Eval.int EvalErr.err

example : Term.Diverges (.op .mul (.int 0) .omega) :=
  diverges_op_right (eval_not_evalErr Eval.int) Term.omega_diverges

end Strictness

namespace Strictness

open Term

/-- Regression checks for the agreed `if` convention. -/
example : RootStep (.ite (.int 3) (.int 1) (.int 2)) (.int 1) :=
  RootStep.ifTrue (by decide)

example : RootStep (.ite (.int (-4)) (.int 1) (.int 2)) (.int 1) :=
  RootStep.ifTrue (by decide)

example : RootStep (.ite (.int 0) (.int 1) (.int 2)) (.int 2) :=
  RootStep.ifFalse

/-- Each evaluation-context frame forwards the semantic error marker. -/
example : EvalErr (EvalCtx.plug (.appFun .hole (.int 0)) .err) := by simp
example : EvalErr (EvalCtx.plug (.proj true .hole) .err) := by simp
example : EvalErr (EvalCtx.plug (.opLeft o .hole (.int 0)) .err) := by simp
example : EvalErr (EvalCtx.plug (.opRight o 0 .hole) .err) := by simp
example : EvalErr (EvalCtx.plug (.ite .hole (.int 1) (.int 2)) .err) := by simp

example : EvalCtx.Demanded (.op o (.var 0) (.int 1)) :=
  ⟨.opLeft o .hole (.int 1), rfl⟩

example : EvalErr (Substitution.apply (singleSubst .err) (.op o (.var 0) (.int 1))) := by
  apply EvalCtx.demanded_err
  exact ⟨.opLeft o .hole (.int 1), rfl⟩

end Strictness
