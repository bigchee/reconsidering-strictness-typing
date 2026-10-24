import Strictness.Operational.Properties

/-!
The open call-by-name closure machine.

Defines closures, environments, continuations and transitions, and proves
transition determinism and terminality of demanded variables and errors.
-/

namespace Strictness

/-- Closures for the open call-by-name machine.  An environment entry is
`some` delayed closure or `none` for an unresolved source variable.  The
latter is the machine-level representation of the paper's `E[x]` terminal
form. -/
inductive Closure where
  | mk : Term → List (Option Closure) → Closure

namespace Closure

def lookup : List (Option Closure) → Nat → Option (Option Closure)
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => lookup xs n

end Closure

/-- CBN continuation frames.  There are no frames below lambda bodies, pair
components, or function arguments. -/
inductive Kont where
  | app : Closure → Kont
  | proj : Bool → Kont
  | opLeft : PrimOp → Closure → Kont
  | opRight : PrimOp → Int → Kont
  | ite : Closure → Closure → Kont

structure MachineState where
  focus : Closure
  kont : List Kont

namespace MachineState

def open1 (e : Term) : MachineState :=
  ⟨.mk e [none], []⟩

def closed1 (a e : Term) : MachineState :=
  ⟨.mk e [some (.mk a [])], []⟩

/-- The machine has reached the unresolved variable in an evaluation
position.  The continuation is the evaluation context `E`. -/
def Demands (s : MachineState) : Prop :=
  match s.focus with
  | .mk (.var i) env => Closure.lookup env i = some none
  | _ => False

def IsError (s : MachineState) : Prop :=
  match s.focus with
  | .mk .err _ => True
  | _ => False

end MachineState

/-- One transition of the open CBN closure machine. -/
inductive MachineStep : MachineState → MachineState → Prop where
  | var {i env c k} :
      Closure.lookup env i = some (some c) →
      MachineStep ⟨.mk (.var i) env, k⟩ ⟨c, k⟩
  | app {e₁ e₂ env k} :
      MachineStep ⟨.mk (.app e₁ e₂) env, k⟩
        ⟨.mk e₁ env, .app (.mk e₂ env) :: k⟩
  | proj {b e env k} :
      MachineStep ⟨.mk (.proj b e) env, k⟩
        ⟨.mk e env, .proj b :: k⟩
  | op (o : PrimOp) {e₁ e₂ env k} :
      MachineStep ⟨.mk (.op o e₁ e₂) env, k⟩
        ⟨.mk e₁ env, .opLeft o (.mk e₂ env) :: k⟩
  | ite {e₀ e₁ e₂ env k} :
      MachineStep ⟨.mk (.ite e₀ e₁ e₂) env, k⟩
        ⟨.mk e₀ env, .ite (.mk e₁ env) (.mk e₂ env) :: k⟩
  | letE {e₁ e₂ env k} :
      MachineStep ⟨.mk (.letE e₁ e₂) env, k⟩
        ⟨.mk e₂ (some (.mk e₁ env) :: env), k⟩
  | fix {body env k} :
      MachineStep ⟨.mk (.fix body) env, k⟩
        ⟨.mk body (some (.mk (.fix body) env) :: env), k⟩
  | lamApp {body env a k} :
      MachineStep ⟨.mk (.lam body) env, .app a :: k⟩
        ⟨.mk body (some a :: env), k⟩
  | projLeft {e₁ e₂ env k} :
      MachineStep ⟨.mk (.pair e₁ e₂) env, .proj true :: k⟩
        ⟨.mk e₁ env, k⟩
  | projRight {e₁ e₂ env k} :
      MachineStep ⟨.mk (.pair e₁ e₂) env, .proj false :: k⟩
        ⟨.mk e₂ env, k⟩
  | opLeft (o : PrimOp) {n env a k} :
      MachineStep ⟨.mk (.int n) env, .opLeft o a :: k⟩
        ⟨a, .opRight o n :: k⟩
  | opRight (o : PrimOp) {n₁ n₂ env k} :
      MachineStep ⟨.mk (.int n₂) env, .opRight o n₁ :: k⟩
        ⟨.mk (.int (o.eval n₁ n₂)) env, k⟩
  | ifTrue {n t f env k} : n ≠ 0 →
      MachineStep ⟨.mk (.int n) env, .ite t f :: k⟩ ⟨t, k⟩
  | ifFalse {t f env k} :
      MachineStep ⟨.mk (.int 0) env, .ite t f :: k⟩ ⟨f, k⟩
  /-- `omega` is the semantic divergent computation used by the logical
  relation.  Its self transition keeps the machine's terminal states aligned
  with the source reduction semantics. -/
  | omega {env k} :
      MachineStep ⟨.mk .omega env, k⟩ ⟨.mk .omega env, k⟩

/-- Finite machine execution. -/
inductive MachineSteps (s : MachineState) : MachineState → Prop where
  | refl : MachineSteps s s
  | tail {s' s''} : MachineSteps s s' → MachineStep s' s'' → MachineSteps s s''

/-- The closure machine has a unique next state. -/
theorem machineStep_deterministic {s t u : MachineState}
    (hLeft : MachineStep s t) (hRight : MachineStep s u) : t = u := by
  cases hLeft <;> cases hRight
  case var.var =>
    rename_i i env c₁ k h₁ c₂ h₂
    rw [h₁] at h₂
    cases h₂
    rfl
  case ifTrue.ifFalse hn =>
    exact False.elim (hn rfl)
  case ifFalse.ifTrue hn =>
    exact False.elim (hn rfl)
  all_goals rfl

namespace MachineState

/-- A machine terminal has no outgoing CBN transition.  `Demands` is the
machine representation of the paper's terminal observation `E[x]`. -/
def Terminal (s : MachineState) : Prop := ∀ s', ¬ MachineStep s s'

/-- A completed integer observation has no remaining continuation frames. -/
def ReturnsInt (s : MachineState) (n : Int) : Prop :=
  ∃ env, s = ⟨.mk (.int n) env, []⟩

end MachineState


namespace MachineState

/-- An unresolved environment entry is a genuine machine terminal: no
transition can silently pass a demanded source variable. -/
theorem demands_no_step {s s' : MachineState} (hDemand : Demands s) :
    ¬ MachineStep s s' := by
  intro h
  rcases s with ⟨⟨e, env⟩, k⟩
  cases e with
  | var i =>
    change Closure.lookup env i = some none at hDemand
    cases h with
    | var hClosed => rw [hDemand] at hClosed; cases hClosed
  | int n => simp [Demands] at hDemand
  | lam body => simp [Demands] at hDemand
  | fix body => simp [Demands] at hDemand
  | app e₁ e₂ => simp [Demands] at hDemand
  | pair e₁ e₂ => simp [Demands] at hDemand
  | proj b e => simp [Demands] at hDemand
  | op o e₁ e₂ => simp [Demands] at hDemand
  | ite e₀ e₁ e₂ => simp [Demands] at hDemand
  | letE e₁ e₂ => simp [Demands] at hDemand
  | omega => simp [Demands] at hDemand
  | err => simp [Demands] at hDemand

/-- The semantic error marker is also terminal in the machine; an enclosing
continuation records the evaluation context which demanded it. -/
theorem error_no_step {s s' : MachineState} (hError : IsError s) :
    ¬ MachineStep s s' := by
  intro h
  rcases s with ⟨⟨e, env⟩, k⟩
  cases e <;> simp [IsError] at hError
  cases h

end MachineState

end Strictness
