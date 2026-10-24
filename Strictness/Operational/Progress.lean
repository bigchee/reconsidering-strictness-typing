import Strictness.Operational.Preservation
import Strictness.Operational.Observations
import Strictness.Operational.Properties

namespace Strictness

/-- An in-scope free variable occupies the current evaluation position. -/
def VariableFocused (Γ : Term.Ctx) (q : Term) : Prop :=
  ∃ i, i < Γ.length ∧ ∃ E, q = EvalCtx.plug E (.var i)

/-- Wrapping a blocked focus in an evaluation context preserves its kind. -/
theorem focused_blocked_plug
    (E : EvalCtx) {Γ : Term.Ctx} {q : Term}
    (h : VariableFocused Γ q ∨ ErrorFocused q) :
    VariableFocused Γ (EvalCtx.plug E q) ∨
      ErrorFocused (EvalCtx.plug E q) := by
  rcases h with hVar | hErr
  · rcases hVar with ⟨i, hi, F, rfl⟩
    exact Or.inl ⟨i, hi, EvalCtx.compose E F,
      (EvalCtx.plug_compose E F (.var i)).symm⟩
  · rcases hErr with ⟨F, rfl⟩
    exact Or.inr ⟨EvalCtx.compose E F,
      (EvalCtx.plug_compose E F .err).symm⟩

/-- Open-term progress: a simply typed term can step, is a head value,
or is blocked on an in-scope variable or an exposed error marker.
Lambda bodies, pair components, and application arguments are not forced. -/
theorem typed_progress_open
    {Γ : Term.Ctx} {e : Term} {τ : SimpleTy}
    (h : Term.HasType Γ e τ) :
    (∃ e', Step e e') ∨ HeadValue e ∨
      VariableFocused Γ e ∨ ErrorFocused e := by
  induction h with
  | var hLookup =>
      exact .inr (.inr (.inl
        ⟨_, simple_lookup_lt_length hLookup, .hole, rfl⟩))
  | int => exact .inr (.inl (.int _))
  | lam hBody ih => exact .inr (.inl (.lam _))
  | app hFun hArg ihFun ihArg =>
      rcases ihFun with ⟨e', hStep⟩ | hVal | hBlocked
      · exact .inl ⟨_, step_appFun _ hStep⟩
      · cases hVal with
        | lam body => exact .inl ⟨_, ⟨.hole, _, _, .beta, rfl, rfl⟩⟩
        | int n => cases hFun
        | pair e₁ e₂ => cases hFun
      · exact .inr (.inr
          (focused_blocked_plug (.appFun .hole _) hBlocked))
  | pair h₁ h₂ ih₁ ih₂ => exact .inr (.inl (.pair _ _))
  | projLeft hPair ih =>
      rcases ih with ⟨e', hStep⟩ | hVal | hBlocked
      · exact .inl ⟨_, step_projFrame true hStep⟩
      · cases hVal with
        | pair e₁ e₂ => exact .inl ⟨_, ⟨.hole, _, _, .projLeft, rfl, rfl⟩⟩
        | int n => cases hPair
        | lam body => cases hPair
      · exact .inr (.inr
          (focused_blocked_plug (.proj true .hole) hBlocked))
  | projRight hPair ih =>
      rcases ih with ⟨e', hStep⟩ | hVal | hBlocked
      · exact .inl ⟨_, step_projFrame false hStep⟩
      · cases hVal with
        | pair e₁ e₂ => exact .inl ⟨_, ⟨.hole, _, _, .projRight, rfl, rfl⟩⟩
        | int n => cases hPair
        | lam body => cases hPair
      · exact .inr (.inr
          (focused_blocked_plug (.proj false .hole) hBlocked))
  | op o hLeft hRight ihLeft ihRight =>
      rcases ihLeft with ⟨e', hStep⟩ | hVal | hBlocked
      · exact .inl ⟨_, step_opLeftFrame _ hStep⟩
      · cases hVal with
        | int n₁ =>
            rcases ihRight with ⟨e', hStep⟩ | hVal | hBlocked
            · exact .inl ⟨_, step_opRightFrame n₁ hStep⟩
            · cases hVal with
              | int n₂ => exact .inl ⟨_, ⟨.hole, _, _, .op o, rfl, rfl⟩⟩
              | lam body => cases hRight
              | pair e₁ e₂ => cases hRight
            · exact .inr (.inr
                (focused_blocked_plug (.opRight o n₁ .hole) hBlocked))
        | lam body => cases hLeft
        | pair e₁ e₂ => cases hLeft
      · exact .inr (.inr
          (focused_blocked_plug (.opLeft o .hole _) hBlocked))
  | ite hCond hThen hElse ihCond ihThen ihElse =>
      rcases ihCond with ⟨e', hStep⟩ | hVal | hBlocked
      · exact .inl ⟨_, step_iteFrame _ _ hStep⟩
      · cases hVal with
        | int n =>
            by_cases hn : n = 0
            · subst n
              exact .inl ⟨_, ⟨.hole, _, _, .ifFalse, rfl, rfl⟩⟩
            · exact .inl ⟨_, ⟨.hole, _, _, .ifTrue hn, rfl, rfl⟩⟩
        | lam body => cases hCond
        | pair e₁ e₂ => cases hCond
      · exact .inr (.inr
          (focused_blocked_plug (.ite .hole _ _) hBlocked))
  | letE hDef hBody ihDef ihBody =>
      exact .inl ⟨_, ⟨.hole, _, _, .letE, rfl, rfl⟩⟩
  | fix hBody ihBody =>
      exact .inl ⟨_, ⟨.hole, _, _, .fix, rfl, rfl⟩⟩
  | omega => exact .inl ⟨_, ⟨.hole, _, _, .omega, rfl, rfl⟩⟩
  | err => exact .inr (.inr (.inr ⟨.hole, rfl⟩))

/-- A term is terminal when no CBN source step is available. -/
def SmallStepTerminal (q : Term) : Prop :=
  ∀ q', ¬ Step q q'

/-- With a singleton context, a focused in-scope variable is var 0. -/
theorem variableFocused_singleton_demands
    {σ : SimpleTy} {q : Term}
    (h : VariableFocused [σ] q) :
    EvalCtx.Demanded q := by
  rcases h with ⟨i, hi, E, hEq⟩
  have hiZero : i = 0 := by
    simp only [List.length_singleton] at hi
    omega
  subst i
  exact ⟨E, hEq⟩

/-- A terminal open integer term is blocked on the single free variable,
exposes an error, or is a completed integer. -/
theorem typed_open_int_terminal_forms
    {σ : SimpleTy} {q : Term}
    (hType : Term.HasType [σ] q .int)
    (hTerminal : SmallStepTerminal q) :
    EvalCtx.Demanded q ∨ ErrorFocused q ∨ ∃ n, q = .int n := by
  rcases typed_progress_open hType with
    ⟨q', hStep⟩ | hVal | hVar | hError
  · exact False.elim (hTerminal q' hStep)
  · cases hVal with
    | int n =>
        exact .inr (.inr ⟨n, rfl⟩)
    | lam body =>
        cases hType
    | pair e₁ e₂ =>
        cases hType
  · exact .inl (variableFocused_singleton_demands hVar)
  · exact .inr (.inl hError)

/-- A head value cannot be an evaluation context focused on a variable. -/
theorem headValue_not_plug_var
    {v : Term} (hVal : HeadValue v) (E : EvalCtx) (i : Nat) :
    v ≠ EvalCtx.plug E (.var i) := by
  cases E <;> intro hEq <;> cases hVal <;> cases hEq

/-- No primitive contraction starts from a variable-focused context. -/
theorem rootStep_not_plug_var
    {r r' : Term} (hRoot : RootStep r r') (E : EvalCtx) (i : Nat) :
    r ≠ EvalCtx.plug E (.var i) := by
  intro hEq
  cases hRoot <;> cases E <;> simp only [EvalCtx.plug] at hEq
  all_goals first
    | exact headValue_not_plug_var
        (HeadValue.lam _) _ _ (Term.app.inj hEq).1
    | exact headValue_not_plug_var
        (HeadValue.pair _ _) _ _ (Term.proj.inj hEq).2
    | exact headValue_not_plug_var
        (HeadValue.int _) _ _ (Term.op.inj hEq).2.1
    | exact headValue_not_plug_var
        (HeadValue.int _) _ _ (Term.op.inj hEq).2.2
    | exact headValue_not_plug_var
        (HeadValue.int _) _ _ (Term.ite.inj hEq).1
    | cases hEq

/-- Head values admit no contextual CBN step. -/
theorem headValue_smallStep_terminal
    {q : Term} (hVal : HeadValue q) :
    SmallStepTerminal q := by
  intro q' hStep
  rcases hStep with ⟨F, r, r', hRoot, rfl, hEnd⟩
  cases F <;> simp only [EvalCtx.plug] at hVal
  all_goals cases hVal <;> cases hRoot

/-- Evaluation contexts focused on any free variable are terminal.
The variable index need not satisfy a typing or scope assumption. -/
theorem evalCtx_var_smallStep_terminal
    (E : EvalCtx) (i : Nat) :
    SmallStepTerminal (EvalCtx.plug E (.var i)) := by
  induction E with
  | hole =>
      intro q' hStep
      rcases hStep with ⟨F, r, r', hRoot, hEq, hEnd⟩
      cases F <;> simp only [EvalCtx.plug] at hEq
      · subst r
        cases hRoot
      all_goals cases hEq
  | appFun E a ih =>
      intro q' hStep
      rcases hStep with ⟨F, r, r', hRoot, hEq, hEnd⟩
      cases F with
      | hole =>
          exact rootStep_not_plug_var hRoot (.appFun E a) i hEq.symm
      | appFun F b =>
          exact ih (EvalCtx.plug F r')
            ⟨F, r, r', hRoot, (Term.app.inj hEq).1, rfl⟩
      | proj b F => cases hEq
      | opLeft o F b => cases hEq
      | opRight o n F => cases hEq
      | ite F t f => cases hEq
  | proj b E ih =>
      intro q' hStep
      rcases hStep with ⟨F, r, r', hRoot, hEq, hEnd⟩
      cases F with
      | hole =>
          exact rootStep_not_plug_var hRoot (.proj b E) i hEq.symm
      | appFun F a => cases hEq
      | proj c F =>
          exact ih (EvalCtx.plug F r')
            ⟨F, r, r', hRoot, (Term.proj.inj hEq).2, rfl⟩
      | opLeft o F a => cases hEq
      | opRight o n F => cases hEq
      | ite F t f => cases hEq
  | opLeft o E a ih =>
      intro q' hStep
      rcases hStep with ⟨F, r, r', hRoot, hEq, hEnd⟩
      cases F with
      | hole =>
          exact rootStep_not_plug_var hRoot (.opLeft o E a) i hEq.symm
      | appFun F b => cases hEq
      | proj b F => cases hEq
      | opLeft o F b =>
          exact ih (EvalCtx.plug F r')
            ⟨F, r, r', hRoot, (Term.op.inj hEq).2.1, rfl⟩
      | opRight o n F =>
          exact headValue_not_plug_var
            (HeadValue.int n) E i (Term.op.inj hEq).2.1.symm
      | ite F t f => cases hEq
  | opRight o n E ih =>
      intro q' hStep
      rcases hStep with ⟨F, r, r', hRoot, hEq, hEnd⟩
      cases F with
      | hole =>
          exact rootStep_not_plug_var hRoot (.opRight o n E) i hEq.symm
      | appFun F a => cases hEq
      | proj b F => cases hEq
      | opLeft o F a =>
          exact headValue_smallStep_terminal (HeadValue.int n)
            (EvalCtx.plug F r')
            ⟨F, r, r', hRoot, (Term.op.inj hEq).2.1, rfl⟩
      | opRight o m F =>
          exact ih (EvalCtx.plug F r')
            ⟨F, r, r', hRoot, (Term.op.inj hEq).2.2, rfl⟩
      | ite F t f => cases hEq
  | ite E t f ih =>
      intro q' hStep
      rcases hStep with ⟨F, r, r', hRoot, hEq, hEnd⟩
      cases F with
      | hole =>
          exact rootStep_not_plug_var hRoot (.ite E t f) i hEq.symm
      | appFun F a => cases hEq
      | proj b F => cases hEq
      | opLeft o F a => cases hEq
      | opRight o n F => cases hEq
      | ite F a b =>
          exact ih (EvalCtx.plug F r')
            ⟨F, r, r', hRoot, (Term.ite.inj hEq).1, rfl⟩

/-- A demanded occurrence of the single free variable is terminal. -/
theorem demanded_smallStep_terminal
    {q : Term} (hDemand : EvalCtx.Demanded q) :
    SmallStepTerminal q := by
  rcases hDemand with ⟨E, rfl⟩
  exact evalCtx_var_smallStep_terminal E 0

end Strictness
