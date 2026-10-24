import Strictness.Language.SimpleTyping

namespace Strictness

/-- Values produced by the CBN big-step semantics.

Pairs retain their components unevaluated; lambdas retain their bodies.
Thus values are head-normal forms rather than fully evaluated terms.
-/
inductive Value where
  | int : Int → Value
  | pair : Term → Term → Value
  | lam : Term → Value
  deriving DecidableEq, Repr

namespace Value

/-- The term corresponding to a semantic value. -/
def toTerm : Value → Term
  | .int n => .int n
  | .pair e₁ e₂ => .pair e₁ e₂
  | .lam body => .lam body

end Value

/-- CBN natural/big-step evaluation to a head-normal-form value. -/
inductive Eval : Term → Value → Prop where
  | int {n : Int} : Eval (.int n) (.int n)
  | lam {body : Term} : Eval (.lam body) (.lam body)
  | pair {e₁ e₂ : Term} : Eval (.pair e₁ e₂) (.pair e₁ e₂)
  | app {e₁ e₂ body : Term} {v : Value} :
      Eval e₁ (.lam body) →
      Eval (Term.instantiate body e₂) v →
      Eval (.app e₁ e₂) v
  | projLeft {e e₁ e₂ : Term} {v : Value} :
      Eval e (.pair e₁ e₂) →
      Eval e₁ v →
      Eval (.proj true e) v
  | projRight {e e₁ e₂ : Term} {v : Value} :
      Eval e (.pair e₁ e₂) →
      Eval e₂ v →
      Eval (.proj false e) v
  | op (o : PrimOp) {e₁ e₂ : Term} {n₁ n₂ : Int} :
      Eval e₁ (.int n₁) →
      Eval e₂ (.int n₂) →
      Eval (.op o e₁ e₂) (.int (o.eval n₁ n₂))
  | ifZero {e₀ e₁ e₂ : Term} {n : Int} {v : Value} :
      Eval e₀ (.int n) →
      n = 0 →
      Eval e₂ v →
      Eval (.ite e₀ e₁ e₂) v
  | ifNonzero {e₀ e₁ e₂ : Term} {n : Int} {v : Value} :
      Eval e₀ (.int n) →
      n ≠ 0 →
      Eval e₁ v →
      Eval (.ite e₀ e₁ e₂) v
  | letE {e₁ e₂ : Term} {v : Value} :
      Eval (Term.instantiate e₂ e₁) v →
      Eval (.letE e₁ e₂) v
  | fix {body : Term} {v : Value} :
      Eval (Term.instantiate body (.fix body)) v →
      Eval (.fix body) v

/-- Evaluation to the semantic error marker.

Only demanded/evaluation-position occurrences propagate `err`; a pair or
lambda containing `err` does not itself evaluate to an error until that
component/body is demanded.
-/
inductive EvalErr : Term → Prop where
  | err : EvalErr .err
  | appFun {e₁ e₂ : Term} :
      EvalErr e₁ →
      EvalErr (.app e₁ e₂)
  | appBody {e₁ e₂ body : Term} :
      Eval e₁ (.lam body) →
      EvalErr (Term.instantiate body e₂) →
      EvalErr (.app e₁ e₂)
  | projScrutinee {b : Bool} {e : Term} :
      EvalErr e →
      EvalErr (.proj b e)
  | projLeftComponent {e e₁ e₂ : Term} :
      Eval e (.pair e₁ e₂) →
      EvalErr e₁ →
      EvalErr (.proj true e)
  | projRightComponent {e e₁ e₂ : Term} :
      Eval e (.pair e₁ e₂) →
      EvalErr e₂ →
      EvalErr (.proj false e)
  | opLeft (o : PrimOp) {e₁ e₂ : Term} :
      EvalErr e₁ →
      EvalErr (.op o e₁ e₂)
  | opRight (o : PrimOp) {e₁ e₂ : Term} {n₁ : Int} :
      Eval e₁ (.int n₁) →
      EvalErr e₂ →
      EvalErr (.op o e₁ e₂)
  | ifCond {e₀ e₁ e₂ : Term} :
      EvalErr e₀ →
      EvalErr (.ite e₀ e₁ e₂)
  | ifZeroBranch {e₀ e₁ e₂ : Term} {n : Int} :
      Eval e₀ (.int n) →
      n = 0 →
      EvalErr e₂ →
      EvalErr (.ite e₀ e₁ e₂)
  | ifNonzeroBranch {e₀ e₁ e₂ : Term} {n : Int} :
      Eval e₀ (.int n) →
      n ≠ 0 →
      EvalErr e₁ →
      EvalErr (.ite e₀ e₁ e₂)
  | letBody {e₁ e₂ : Term} :
      EvalErr (Term.instantiate e₂ e₁) →
      EvalErr (.letE e₁ e₂)
  | fix {body : Term} :
      EvalErr (Term.instantiate body (.fix body)) →
      EvalErr (.fix body)

namespace Term

/-- A semantic error is distinct from divergence. -/
def Diverges (e : Term) : Prop :=
  (¬ ∃ v, Eval e v) ∧ ¬ EvalErr e

end Term

namespace Value

/-- Simple types of semantic values, once the retained components/body are typed.

This is only a helper predicate; the main semantic sets use `Term.HasType`.
-/
def HasSimpleType (σ : SimpleTy) : Value → Prop
  | .int _ => σ = .int
  | .pair e₁ e₂ => ∃ τ₁ τ₂, σ = .prod τ₁ τ₂ ∧
      Term.HasType [] e₁ τ₁ ∧ Term.HasType [] e₂ τ₂
  | .lam body => ∃ τ₁ τ₂, σ = .arrow τ₁ τ₂ ∧ Term.HasType (τ₁ :: []) body τ₂

end Value

/-- The call-by-name semantics treats zero as false and every non-zero integer
as true.  This is the convention fixed for the formalization. -/
def IfConditionTrue (n : Int) : Prop := n ≠ 0

end Strictness
