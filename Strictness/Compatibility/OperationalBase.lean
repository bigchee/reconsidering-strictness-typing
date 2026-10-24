import Strictness.Operational.SmallStep

/-!
Finite-observation reflection along source reduction.

Primitive contractions and their evaluation-context closures preserve
big-step value and error observations backwards. No typing or closedness
assumption is needed. These lemmas also support closure-machine adequacy.
The converse direction and observation equivalences are in
`Strictness.Compatibility.Operational`.
-/

namespace Strictness

/-- Every primitive contraction is reflected by the big-step
observations, without typing or closedness assumptions. -/
theorem rootStep_eval {r r' : Term} (h : RootStep r r') {v : Value} :
    Eval r' v → Eval r v := by
  intro hr
  cases h with
  | beta => exact Eval.app Eval.lam hr
  | projLeft => exact Eval.projLeft Eval.pair hr
  | projRight => exact Eval.projRight Eval.pair hr
  | op o => cases hr; exact Eval.op o Eval.int Eval.int
  | ifTrue hn => exact Eval.ifNonzero Eval.int hn hr
  | ifFalse => exact Eval.ifZero Eval.int rfl hr
  | letE => exact Eval.letE hr
  | fix => exact Eval.fix hr
  | omega => exact hr

theorem rootStep_evalErr {r r' : Term} (h : RootStep r r') :
    EvalErr r' → EvalErr r := by
  intro hr
  cases h with
  | beta => exact EvalErr.appBody Eval.lam hr
  | projLeft => exact EvalErr.projLeftComponent Eval.pair hr
  | projRight => exact EvalErr.projRightComponent Eval.pair hr
  | op o => cases hr
  | ifTrue hn => exact EvalErr.ifNonzeroBranch Eval.int hn hr
  | ifFalse => exact EvalErr.ifZeroBranch Eval.int rfl hr
  | letE => exact EvalErr.letBody hr
  | fix => exact EvalErr.fix hr
  | omega => exact hr

theorem rootStep_context_eval (E : EvalCtx) {r r' v} (hRoot : RootStep r r') :
    Eval (EvalCtx.plug E r') v → Eval (EvalCtx.plug E r) v := by
  intro hEval
  induction E generalizing r r' v with
  | hole => exact rootStep_eval hRoot hEval
  | appFun E a ih =>
    cases hEval with
    | app hFun hBody => exact .app (ih hRoot hFun) hBody
  | proj b E ih =>
    cases b with
    | false =>
      cases hEval with
      | projRight hPair hComp => exact .projRight (ih hRoot hPair) hComp
    | true =>
      cases hEval with
      | projLeft hPair hComp => exact .projLeft (ih hRoot hPair) hComp
  | opLeft o E a ih =>
    cases hEval with
    | op o hLeft hRight => exact .op o (ih hRoot hLeft) hRight
  | opRight o n E ih =>
    cases hEval with
    | op o hLeft hRight => exact .op o hLeft (ih hRoot hRight)
  | ite E t f ih =>
    cases hEval with
    | ifZero hCond hn hBranch => exact .ifZero (ih hRoot hCond) hn hBranch
    | ifNonzero hCond hn hBranch => exact .ifNonzero (ih hRoot hCond) hn hBranch

theorem rootStep_context_evalErr (E : EvalCtx) {r r'} (hRoot : RootStep r r') :
    EvalErr (EvalCtx.plug E r') → EvalErr (EvalCtx.plug E r) := by
  intro hErr
  induction E generalizing r r' with
  | hole => exact rootStep_evalErr hRoot hErr
  | appFun E a ih =>
    cases hErr with
    | appFun hFun => exact .appFun (ih hRoot hFun)
    | appBody hFun hBody => exact .appBody (rootStep_context_eval E hRoot hFun) hBody
  | proj b E ih =>
    cases b with
    | false =>
      cases hErr with
      | projScrutinee hScrut => exact .projScrutinee (ih hRoot hScrut)
      | projRightComponent hPair hComp =>
        exact .projRightComponent (rootStep_context_eval E hRoot hPair) hComp
    | true =>
      cases hErr with
      | projScrutinee hScrut => exact .projScrutinee (ih hRoot hScrut)
      | projLeftComponent hPair hComp =>
        exact .projLeftComponent (rootStep_context_eval E hRoot hPair) hComp
  | opLeft o E a ih =>
    cases hErr with
    | opLeft o hLeft => exact .opLeft o (ih hRoot hLeft)
    | opRight o hLeft hRight =>
      exact .opRight o (rootStep_context_eval E hRoot hLeft) hRight
  | opRight o n E ih =>
    cases hErr with
    | opLeft o hLeft => cases hLeft
    | opRight o hLeft hRight => exact .opRight o hLeft (ih hRoot hRight)
  | ite E t f ih =>
    cases hErr with
    | ifCond hCond => exact .ifCond (ih hRoot hCond)
    | ifZeroBranch hCond hn hBranch =>
      exact .ifZeroBranch (rootStep_context_eval E hRoot hCond) hn hBranch
    | ifNonzeroBranch hCond hn hBranch =>
      exact .ifNonzeroBranch (rootStep_context_eval E hRoot hCond) hn hBranch

theorem step_evalErr {e e'} (hStep : Step e e') : EvalErr e' → EvalErr e := by
  intro hErr
  rcases hStep with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact rootStep_context_evalErr E hRoot hErr

theorem steps_evalErr {e e'} (hSteps : Steps e e') : EvalErr e' → EvalErr e := by
  intro hErr
  induction hSteps with
  | refl => exact hErr
  | tail hSteps hStep ih => exact ih (step_evalErr hStep hErr)

theorem step_eval {e e' v} (hStep : Step e e') : Eval e' v → Eval e v := by
  intro hEval
  rcases hStep with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact rootStep_context_eval E hRoot hEval

theorem steps_eval {e e' v} (hSteps : Steps e e') : Eval e' v → Eval e v := by
  intro hEval
  induction hSteps with
  | refl => exact hEval
  | tail hSteps hStep ih => exact ih (step_eval hStep hEval)

theorem step_diverges_forward {e e' : Term} (hDiv : Term.Diverges e)
    (hStep : Step e e') : Term.Diverges e' := by
  constructor
  · intro hEval
    rcases hEval with ⟨v, hEval⟩
    exact hDiv.1 ⟨v, step_eval hStep hEval⟩
  · intro hErr
    exact hDiv.2 (step_evalErr hStep hErr)

end Strictness
