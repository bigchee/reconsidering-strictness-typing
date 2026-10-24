import Strictness.Operational.Progress

/-!
Equivalence of big-step and small-step observations.

Constructs finite reductions from value and error evaluations and combines
them with backward reflection. Determinism and terminal observations exclude
finite observation along an infinite execution. Closed simple typing gives
progress for the reverse divergence implication, at every simple type.
The reduction relation stops at `E[err]`; error-propagation transitions are
not part of this correspondence.
-/

namespace Strictness

open Term

namespace Steps

theorem trans {a b c : Term} (hab : Steps a b) (hbc : Steps b c) : Steps a c := by
  induction hbc with
  | refl => exact hab
  | tail _ h ih => exact .tail ih h

theorem plug (E : EvalCtx) {a b : Term} (h : Steps a b) :
    Steps (E.plug a) (E.plug b) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (step_plug E h)

end Steps

private theorem root_steps {a b : Term} (h : RootStep a b) : Steps a b :=
  .tail .refl ⟨.hole, a, b, h, rfl, rfl⟩

/-- Big-step value evaluation gives a finite source reduction, including for open terms. -/
theorem eval_steps {e : Term} {v : Value} (h : Eval e v) : Steps e v.toTerm := by
  induction h with
  | int | lam | pair => exact .refl
  | app hFun hBody ihFun ihBody =>
      exact ((ihFun.plug (.appFun .hole _)).trans (root_steps .beta)).trans ihBody
  | projLeft hPair hComp ihPair ihComp =>
      exact ((ihPair.plug (.proj true .hole)).trans (root_steps .projLeft)).trans ihComp
  | projRight hPair hComp ihPair ihComp =>
      exact ((ihPair.plug (.proj false .hole)).trans (root_steps .projRight)).trans ihComp
  | op o hLeft hRight ihLeft ihRight =>
      exact ((ihLeft.plug (.opLeft o .hole _)).trans
        (ihRight.plug (.opRight o _ .hole))).trans (root_steps (.op o))
  | ifZero hCond hn hBranch ihCond ihBranch =>
      subst hn
      exact ((ihCond.plug (.ite .hole _ _)).trans (root_steps .ifFalse)).trans ihBranch
  | ifNonzero hCond hn hBranch ihCond ihBranch =>
      exact ((ihCond.plug (.ite .hole _ _)).trans (root_steps (.ifTrue hn))).trans ihBranch
  | letE h ih => exact (root_steps .letE).trans ih
  | fix h ih => exact (root_steps .fix).trans ih

theorem eval_iff_steps_value {e : Term} {v : Value} :
    Eval e v ↔ Steps e v.toTerm := by
  constructor
  · exact eval_steps
  · intro h
    apply steps_eval h
    cases v with
    | int => exact .int
    | lam => exact .lam
    | pair => exact .pair

private theorem error_steps_plug (F : EvalCtx) {e : Term}
    (h : ∃ E : EvalCtx, Steps e (E.plug .err)) : ∃ E : EvalCtx, Steps (F.plug e) (E.plug .err) := by
  rcases h with ⟨E, h⟩
  exact ⟨F.compose E, by simpa using h.plug F⟩

/-- Errors stop at an exposed error context; no error-propagation steps are added. -/
theorem evalErr_steps {e : Term} (h : EvalErr e) :
    ∃ E : EvalCtx, Steps e (E.plug .err) := by
  induction h with
  | err => exact ⟨.hole, .refl⟩
  | appFun h ih => exact error_steps_plug (.appFun .hole _) ih
  | projScrutinee h ih => exact error_steps_plug (.proj _ .hole) ih
  | opLeft o h ih => exact error_steps_plug (.opLeft o .hole _) ih
  | ifCond h ih => exact error_steps_plug (.ite .hole _ _) ih
  | appBody hFun hBody ih =>
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (((eval_steps hFun).plug (.appFun .hole _)).trans
        (root_steps .beta)).trans hE⟩
  | projLeftComponent hPair hComp ih =>
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (((eval_steps hPair).plug (.proj true .hole)).trans
        (root_steps .projLeft)).trans hE⟩
  | projRightComponent hPair hComp ih =>
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (((eval_steps hPair).plug (.proj false .hole)).trans
        (root_steps .projRight)).trans hE⟩
  | opRight o hLeft hRight ih =>
      rcases error_steps_plug (.opRight o _ .hole) ih with ⟨E, hE⟩
      exact ⟨E, ((eval_steps hLeft).plug (.opLeft o .hole _)).trans hE⟩
  | ifZeroBranch hCond hn hBranch ih =>
      subst hn
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (((eval_steps hCond).plug (.ite .hole _ _)).trans
        (root_steps .ifFalse)).trans hE⟩
  | ifNonzeroBranch hCond hn hBranch ih =>
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (((eval_steps hCond).plug (.ite .hole _ _)).trans
        (root_steps (.ifTrue hn))).trans hE⟩
  | letBody h ih =>
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (root_steps .letE).trans hE⟩
  | fix h ih =>
      rcases ih with ⟨E, hE⟩
      exact ⟨E, (root_steps .fix).trans hE⟩

theorem evalErr_iff_steps_error {e : Term} :
    EvalErr e ↔ ∃ E : EvalCtx, Steps e (E.plug .err) := by
  refine ⟨evalErr_steps, ?_⟩
  rintro ⟨E, h⟩
  exact steps_evalErr h E.plug_err_evalErr

/-- A deterministic selector used only to prove uniqueness of the existing `Step`. -/
private def nextStep : Term → Option Term
  | .app (.lam body) a => some (instantiate body a)
  | .app f a => (nextStep f).map (fun f' => .app f' a)
  | .proj b (.pair a c) => some (if b then a else c)
  | .proj b e => (nextStep e).map (.proj b)
  | .op o (.int n) (.int m) => some (.int (o.eval n m))
  | .op o (.int n) e => (nextStep e).map (.op o (.int n))
  | .op o e a => (nextStep e).map (fun e' => .op o e' a)
  | .ite (.int n) t f => some (if n = 0 then f else t)
  | .ite e t f => (nextStep e).map (fun e' => .ite e' t f)
  | .letE a body => some (instantiate body a)
  | .fix body => some (instantiate body (.fix body))
  | .omega => some .omega
  | _ => none

private theorem nextStep_plug (E : EvalCtx) {e e' : Term}
    (h : nextStep e = some e') : nextStep (E.plug e) = some (E.plug e') := by
  induction E with
  | hole => exact h
  | appFun E a ih =>
      simp only [EvalCtx.plug]
      generalize E.plug e = q at ih ⊢
      cases q <;> simp_all [nextStep]
  | proj b E ih =>
      simp only [EvalCtx.plug]
      generalize E.plug e = q at ih ⊢
      cases q <;> simp_all [nextStep]
  | opLeft o E a ih =>
      simp only [EvalCtx.plug]
      generalize E.plug e = q at ih ⊢
      cases q <;> simp_all [nextStep]
  | opRight o n E ih =>
      simp only [EvalCtx.plug]
      generalize E.plug e = q at ih ⊢
      cases q <;> simp_all [nextStep]
  | ite E t f ih =>
      simp only [EvalCtx.plug]
      generalize E.plug e = q at ih ⊢
      cases q <;> simp_all [nextStep]

private theorem step_nextStep {e e' : Term} (h : Step e e') :
    nextStep e = some e' := by
  rcases h with ⟨E, r, r', hRoot, rfl, rfl⟩
  apply nextStep_plug E
  cases hRoot <;> simp_all [nextStep]

/-- Determinism holds without typing or closedness assumptions. -/
theorem step_deterministic {e a b : Term} (ha : Step e a) (hb : Step e b) : a = b := by
  exact Option.some.inj ((step_nextStep ha).symm.trans (step_nextStep hb))

private theorem plug_err_not_head (E : EvalCtx) : ¬ HeadValue (E.plug .err) := by
  cases E <;> intro h <;> cases h

private theorem nextStep_plug_err (E : EvalCtx) : nextStep (E.plug .err) = none := by
  induction E with
  | hole => rfl
  | appFun E a ih | proj b E ih | opLeft o E a ih | opRight o n E ih | ite E t f ih =>
      have hNon := plug_err_not_head E
      simp only [EvalCtx.plug]
      generalize E.plug .err = q at ih hNon ⊢
      cases q <;> simp_all [nextStep]
      all_goals first
        | exact False.elim (hNon (.int _))
        | exact False.elim (hNon (.lam _))
        | exact False.elim (hNon (.pair _ _))

/-- Exposed errors are terminal even for open and untyped terms. -/
theorem evalCtx_err_smallStep_terminal (E : EvalCtx) : SmallStepTerminal (E.plug .err) := by
  intro q h
  have heq := step_nextStep h
  rw [nextStep_plug_err] at heq
  cases heq

theorem value_smallStep_terminal (v : Value) : SmallStepTerminal v.toTerm := by
  apply headValue_smallStep_terminal
  cases v with
  | int => exact .int _
  | lam => exact .lam _
  | pair => exact .pair _ _

/-- A finite path must be a prefix of every infinite run from its source. -/
theorem infiniteSteps_forward {e q : Term} (hInf : InfiniteSteps e) (hStep : Step e q) :
    InfiniteSteps q := by
  rcases hInf with ⟨run, hStart, hRun⟩
  refine ⟨fun n => run (n + 1), ?_, fun n => hRun (n + 1)⟩
  exact step_deterministic (by simpa [hStart] using hRun 0) hStep

theorem infiniteSteps_steps {e q : Term} (hInf : InfiniteSteps e) (hSteps : Steps e q) :
    InfiniteSteps q := by
  induction hSteps with
  | refl => exact hInf
  | tail _ h ih => exact infiniteSteps_forward ih h

theorem infiniteSteps_not_terminal {e : Term} (hInf : InfiniteSteps e) :
    ¬ SmallStepTerminal e := by
  rcases hInf with ⟨run, hStart, hRun⟩
  intro hTerminal
  exact hTerminal (run 1) (by simpa [hStart] using hRun 0)

/-- This direction needs neither typing nor closedness. -/
theorem infiniteSteps_diverges {e : Term} (hInf : InfiniteSteps e) : Term.Diverges e := by
  constructor
  · rintro ⟨v, hEval⟩
    exact infiniteSteps_not_terminal (infiniteSteps_steps hInf (eval_steps hEval))
      (value_smallStep_terminal v)
  · intro hErr
    rcases evalErr_steps hErr with ⟨E, hSteps⟩
    exact infiniteSteps_not_terminal (infiniteSteps_steps hInf hSteps)
      (evalCtx_err_smallStep_terminal E)

/-- Closed typing supplies progress at every simple type, including products and arrows. -/
theorem diverges_infiniteSteps {e : Term} {A : SimpleTy}
    (hType : Term.HasType [] e A) (hDiv : Term.Diverges e) : InfiniteSteps e := by
  apply infiniteSteps_of_reachable_can_step
  intro q hSteps
  have hQ := steps_hasType_closed hSteps hType
  rcases typed_progress_of_empty rfl hQ with hStep | hVal | hErr
  · exact hStep
  · have hEval : ∃ v, Eval q v := by
      cases hVal with
      | int n => exact ⟨.int n, .int⟩
      | lam body => exact ⟨.lam body, .lam⟩
      | pair a b => exact ⟨.pair a b, .pair⟩
    rcases hEval with ⟨v, hv⟩
    exact False.elim (hDiv.1 ⟨v, steps_eval hSteps hv⟩)
  · exact False.elim (hDiv.2 (steps_evalErr hSteps hErr))

theorem diverges_iff_infiniteSteps {e : Term} {A : SimpleTy}
    (hType : Term.HasType [] e A) : Term.Diverges e ↔ InfiniteSteps e :=
  ⟨diverges_infiniteSteps hType, infiniteSteps_diverges⟩

/-- Closed typed reduction retains both its simple type and its closedness. -/
theorem steps_closed_typed {e q : Term} {A : SimpleTy}
    (hType : Term.HasType [] e A) (hSteps : Steps e q) :
    Term.Closed q ∧ Term.HasType [] q A := by
  have hQ := steps_hasType_closed hSteps hType
  exact ⟨hasType_closedAt_length hQ, hQ⟩

/-- Progress stated using precisely the two terminal observation forms. -/
theorem closed_typed_progress {e : Term} {A : SimpleTy}
    (hType : Term.HasType [] e A) :
    (∃ v : Value, e = v.toTerm) ∨ ErrorFocused e ∨ ∃ q, Step e q := by
  rcases typed_progress_open hType with hStep | hVal | hVar | hErr
  · exact .inr (.inr hStep)
  · apply Or.inl
    cases hVal with
    | int n => exact ⟨.int n, rfl⟩
    | lam body => exact ⟨.lam body, rfl⟩
    | pair a b => exact ⟨.pair a b, rfl⟩
  · rcases hVar with ⟨i, hi, _⟩
    exact False.elim (Nat.not_lt_zero i hi)
  · exact .inr (.inl hErr)

end Strictness
