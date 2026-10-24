import Strictness.Compatibility.OperationalBase
import Strictness.Operational.OperationalFacts

/-!
General source-level reduction properties.

Collects closed typing preservation, progress, evaluation-context composition,
and infinite execution from persistent progress. These facts are independent
of the closure machine and of the fundamental lemma.
-/

namespace Strictness

/-- Closing substitution leaves a term that is already closed unchanged. -/
theorem substitution_apply_eq_of_closed (ρ : Substitution) {e : Term}
    (hClosed : Term.Closed e) : Substitution.apply ρ e = e := by
  have go : ∀ d e, Term.ClosedAt d e → Substitution.applyAt ρ d e = e := by
    intro d e h
    induction e generalizing d with
    | var i =>
      simp only [Term.ClosedAt] at h
      simp [Substitution.applyAt, h]
    | int n => rfl
    | lam body ih => simp [Substitution.applyAt, ih (d + 1) h]
    | fix body ih => simp [Substitution.applyAt, ih (d + 1) h]
    | app e₁ e₂ ih₁ ih₂ => simp [Substitution.applyAt, ih₁ d h.1, ih₂ d h.2]
    | pair e₁ e₂ ih₁ ih₂ => simp [Substitution.applyAt, ih₁ d h.1, ih₂ d h.2]
    | proj b e ih => simp [Substitution.applyAt, ih d h]
    | op o e₁ e₂ ih₁ ih₂ => simp [Substitution.applyAt, ih₁ d h.1, ih₂ d h.2]
    | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      simp [Substitution.applyAt, ih₀ d h.1, ih₁ d h.2.1, ih₂ d h.2.2]
    | letE e₁ e₂ ih₁ ih₂ =>
      simp [Substitution.applyAt, ih₁ d h.1, ih₂ (d + 1) h.2]
    | omega => rfl
    | err => rfl
  exact go 0 e hClosed

theorem simple_lookup_lt_length : ∀ {Γ : Term.Ctx} {i : Nat} {τ : SimpleTy},
    Term.lookup Γ i = some τ → i < Γ.length
  | [], _, _, h => by simp [Term.lookup] at h
  | _ :: Γ, 0, _, _ => by simp
  | _ :: Γ, i + 1, τ, h => by
      simp only [Term.lookup] at h
      exact Nat.succ_lt_succ (simple_lookup_lt_length h)

theorem hasType_closedAt_length {Γ : Term.Ctx} {e : Term} {τ : SimpleTy}
    (h : Term.HasType Γ e τ) : Term.ClosedAt Γ.length e := by
  induction h with
  | var h => exact simple_lookup_lt_length h
  | int => trivial
  | lam h ih => simpa [Term.ClosedAt, List.length_cons, Nat.add_comm] using ih
  | fix h ih => simpa [Term.ClosedAt, List.length_cons, Nat.add_comm] using ih
  | app h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | pair h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | projLeft h ih => exact ih
  | projRight h ih => exact ih
  | op o h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | ite h₀ h₁ h₂ ih₀ ih₁ ih₂ => exact ⟨ih₀, ih₁, ih₂⟩
  | letE h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | omega => trivial
  | err => trivial

theorem substitution_applyAt_eq_of_closedAt (ρ : Substitution) {d e}
    (hClosed : Term.ClosedAt d e) : Substitution.applyAt ρ d e = e := by
  induction e generalizing d with
  | var i =>
    simp only [Term.ClosedAt] at hClosed
    simp [Substitution.applyAt, hClosed]
  | int n => rfl
  | lam body ih => simp [Substitution.applyAt, ih hClosed]
  | fix body ih => simp [Substitution.applyAt, ih hClosed]
  | app e₁ e₂ ih₁ ih₂ => simp [Substitution.applyAt, ih₁ hClosed.1, ih₂ hClosed.2]
  | pair e₁ e₂ ih₁ ih₂ => simp [Substitution.applyAt, ih₁ hClosed.1, ih₂ hClosed.2]
  | proj b e ih => simp [Substitution.applyAt, ih hClosed]
  | op o e₁ e₂ ih₁ ih₂ => simp [Substitution.applyAt, ih₁ hClosed.1, ih₂ hClosed.2]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp [Substitution.applyAt, ih₀ hClosed.1, ih₁ hClosed.2.1, ih₂ hClosed.2.2]
  | letE e₁ e₂ ih₁ ih₂ =>
    simp [Substitution.applyAt, ih₁ hClosed.1, ih₂ hClosed.2]
  | omega => rfl
  | err => rfl

theorem hasType_instantiate_closed {σ τ : SimpleTy} {body arg : Term}
    (hBody : Term.HasType [σ] body τ) (hArg : Term.HasType [] arg σ) :
    Term.HasType [] (Term.instantiate body arg) τ := by
  let ρ : Substitution := singleSubst arg
  have hArgClosed : Term.Closed arg := Term.hasType_nil_closed hArg
  have hρClosed : ∀ i, Term.Closed (ρ i) := by intro i; exact hArgClosed
  have hApply : Term.HasType [] (Substitution.apply ρ body) τ :=
    Term.hasType_apply hBody (by
      intro i σ' hLookup
      cases i with
      | zero =>
        simp only [Term.lookup] at hLookup
        cases hLookup
        simpa [ρ, singleSubst] using hArg
      | succ i => simp [Term.lookup] at hLookup)
  have hScope : Term.ClosedAt 1 body := by
    simpa using (hasType_closedAt_length hBody)
  have hExtend : Substitution.extend ρ arg = ρ := by
    funext i
    cases i with
    | zero => simp [Substitution.extend, ρ, singleSubst]
    | succ i => simp [Substitution.extend, ρ, singleSubst,
        Term.shift_eq_of_closed hArgClosed]
  have hEq : Substitution.apply ρ body = Term.instantiate body arg := by
    rw [← hExtend, Substitution.apply]
    rw [Substitution.applyAt_extend_eq_subst_of_closed ρ arg hρClosed hArgClosed]
    simp [Term.instantiate, substitution_applyAt_eq_of_closedAt ρ hScope]
  rw [← hEq]
  exact hApply

theorem rootStep_hasType_closed {r r' : Term} {τ : SimpleTy}
    (hRoot : RootStep r r') (hType : Term.HasType [] r τ) :
    Term.HasType [] r' τ := by
  cases hRoot with
  | beta =>
    cases hType with
    | app hFun hArg =>
      cases hFun with
      | lam hBody => exact hasType_instantiate_closed hBody hArg
  | projLeft =>
    cases hType with
    | projLeft hPair =>
      cases hPair with
      | pair hLeft hRight => exact hLeft
  | projRight =>
    cases hType with
    | projRight hPair =>
      cases hPair with
      | pair hLeft hRight => exact hRight
  | op o =>
    cases hType with
    | op o hLeft hRight => exact .int
  | ifTrue hn =>
    cases hType with
    | ite hCond hThen hElse => exact hThen
  | ifFalse =>
    cases hType with
    | ite hCond hThen hElse => exact hElse
  | letE =>
    cases hType with
    | letE hDef hBody => exact hasType_instantiate_closed hBody hDef
  | fix =>
    cases hType with
    | fix hBody =>
      exact hasType_instantiate_closed hBody (Term.HasType.fix hBody)
  | omega => exact hType

theorem rootStep_context_hasType_closed (E : EvalCtx) {r r' : Term} {τ : SimpleTy}
    (hRoot : RootStep r r') (hType : Term.HasType [] (EvalCtx.plug E r) τ) :
    Term.HasType [] (EvalCtx.plug E r') τ := by
  induction E generalizing r r' τ with
  | hole => exact rootStep_hasType_closed hRoot hType
  | appFun E a ih =>
    cases hType with
    | app hFun hArg => exact .app (ih hRoot hFun) hArg
  | proj b E ih =>
    cases b with
    | false =>
      cases hType with
      | projRight hPair => exact .projRight (ih hRoot hPair)
    | true =>
      cases hType with
      | projLeft hPair => exact .projLeft (ih hRoot hPair)
  | opLeft o E a ih =>
    cases hType with
    | op o hLeft hRight => exact .op o (ih hRoot hLeft) hRight
  | opRight o n E ih =>
    cases hType with
    | op o hLeft hRight => exact .op o hLeft (ih hRoot hRight)
  | ite E t f ih =>
    cases hType with
    | ite hCond hThen hElse => exact .ite (ih hRoot hCond) hThen hElse

theorem step_hasType_closed {e e' : Term} {τ : SimpleTy}
    (hStep : Step e e') (hType : Term.HasType [] e τ) : Term.HasType [] e' τ := by
  rcases hStep with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact rootStep_context_hasType_closed E hRoot hType

theorem steps_hasType_closed {e e' : Term} {τ : SimpleTy}
    (hSteps : Steps e e') (hType : Term.HasType [] e τ) : Term.HasType [] e' τ := by
  induction hSteps generalizing τ with
  | refl => exact hType
  | tail hSteps hStep ih => exact step_hasType_closed hStep (ih hType)

/-- Head values of the CBN source semantics.  Pair components and lambda
bodies intentionally remain unevaluated. -/
inductive HeadValue : Term → Prop where
  | int (n : Int) : HeadValue (.int n)
  | lam (body : Term) : HeadValue (.lam body)
  | pair (e₁ e₂ : Term) : HeadValue (.pair e₁ e₂)

theorem step_appFun (a : Term) {e e'} (h : Step e e') : Step (.app e a) (.app e' a) := by
  rcases h with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact ⟨.appFun E a, r, r', hRoot, rfl, rfl⟩

theorem step_projFrame (b : Bool) {e e'} (h : Step e e') :
    Step (.proj b e) (.proj b e') := by
  rcases h with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact ⟨.proj b E, r, r', hRoot, rfl, rfl⟩

theorem step_opLeftFrame (a : Term) {e e'} (h : Step e e') :
    Step (.op o e a) (.op o e' a) := by
  rcases h with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact ⟨.opLeft o E a, r, r', hRoot, rfl, rfl⟩

theorem step_opRightFrame (n : Int) {e e'} (h : Step e e') :
    Step (.op o (.int n) e) (.op o (.int n) e') := by
  rcases h with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact ⟨.opRight o n E, r, r', hRoot, rfl, rfl⟩

theorem step_iteFrame (t f : Term) {e e'} (h : Step e e') :
    Step (.ite e t f) (.ite e' t f) := by
  rcases h with ⟨E, r, r', hRoot, he, he'⟩
  subst e
  subst e'
  exact ⟨.ite E t f, r, r', hRoot, rfl, rfl⟩

/-- Progress for closed simply typed CBN terms.  Semantic `err` is observed
as `EvalErr`; semantic `omega` takes its designated self transition. -/
theorem typed_progress_of_empty {Γ : Term.Ctx} {e : Term} {τ : SimpleTy}
    (hEmpty : Γ = []) (h : Term.HasType Γ e τ) :
    (∃ e', Step e e') ∨ HeadValue e ∨ EvalErr e := by
  induction h with
  | var h => simp [hEmpty, Term.lookup] at h
  | int => exact Or.inr (.inl (.int _))
  | lam h ih => exact Or.inr (.inl (.lam _))
  | app hFun hArg ihFun ihArg =>
    rcases ihFun hEmpty with ⟨e', hStep⟩ | hVal | hErr
    · exact .inl ⟨_, step_appFun _ hStep⟩
    · cases hVal with
      | lam body => exact .inl ⟨_, ⟨.hole, _, _, .beta, rfl, rfl⟩⟩
      | int n => cases hFun
      | pair e₁ e₂ => cases hFun
    · exact .inr (.inr (.appFun hErr))
  | pair h₁ h₂ ih₁ ih₂ => exact Or.inr (.inl (.pair _ _))
  | projLeft hPair ih =>
    rcases ih hEmpty with ⟨e', hStep⟩ | hVal | hErr
    · exact .inl ⟨_, step_projFrame true hStep⟩
    · cases hVal with
      | pair e₁ e₂ => exact .inl ⟨_, ⟨.hole, _, _, .projLeft, rfl, rfl⟩⟩
      | int n => cases hPair
      | lam body => cases hPair
    · exact .inr (.inr (.projScrutinee hErr))
  | projRight hPair ih =>
    rcases ih hEmpty with ⟨e', hStep⟩ | hVal | hErr
    · exact .inl ⟨_, step_projFrame false hStep⟩
    · cases hVal with
      | pair e₁ e₂ => exact .inl ⟨_, ⟨.hole, _, _, .projRight, rfl, rfl⟩⟩
      | int n => cases hPair
      | lam body => cases hPair
    · exact .inr (.inr (.projScrutinee hErr))
  | op o hLeft hRight ihLeft ihRight =>
    rcases ihLeft hEmpty with ⟨e', hStep⟩ | hVal | hErr
    · exact .inl ⟨_, step_opLeftFrame _ hStep⟩
    · cases hVal with
      | int n₁ =>
        rcases ihRight hEmpty with ⟨e', hStep⟩ | hVal | hErr
        · exact .inl ⟨_, step_opRightFrame n₁ hStep⟩
        · cases hVal with
          | int n₂ => exact .inl ⟨_, ⟨.hole, _, _, .op o, rfl, rfl⟩⟩
          | lam body => cases hRight
          | pair e₁ e₂ => cases hRight
        · exact .inr (.inr (.opRight o Eval.int hErr))
      | lam body => cases hLeft
      | pair e₁ e₂ => cases hLeft
    · exact .inr (.inr (.opLeft o hErr))
  | ite hCond hThen hElse ihCond ihThen ihElse =>
    rcases ihCond hEmpty with ⟨e', hStep⟩ | hVal | hErr
    · exact .inl ⟨_, step_iteFrame _ _ hStep⟩
    · cases hVal with
      | int n =>
        by_cases hn : n = 0
        · subst n
          exact .inl ⟨_, ⟨.hole, _, _, .ifFalse, rfl, rfl⟩⟩
        · exact .inl ⟨_, ⟨.hole, _, _, .ifTrue hn, rfl, rfl⟩⟩
      | lam body => cases hCond
      | pair e₁ e₂ => cases hCond
    · exact .inr (.inr (.ifCond hErr))
  | letE hDef hBody ihDef ihBody =>
    exact .inl ⟨_, ⟨.hole, _, _, .letE, rfl, rfl⟩⟩
  | fix hBody ihBody =>
    exact .inl ⟨_, ⟨.hole, _, _, .fix, rfl, rfl⟩⟩
  | omega => exact .inl ⟨_, ⟨.hole, _, _, .omega, rfl, rfl⟩⟩
  | err => exact .inr (.inr .err)

theorem divergent_closed_int_can_step {e : Term}
    (hType : Term.HasType [] e .int) (hDiv : Term.Diverges e) :
    ∃ e', Step e e' := by
  rcases typed_progress_of_empty rfl hType with ⟨e', hStep⟩ | hVal | hErr
  · exact ⟨e', hStep⟩
  · cases hVal with
    | int n => exact False.elim (hDiv.1 ⟨.int n, Eval.int⟩)
    | lam body => cases hType
    | pair e₁ e₂ => cases hType
  · exact False.elim (hDiv.2 hErr)


namespace EvalCtx

def compose : EvalCtx → EvalCtx → EvalCtx
  | .hole, F => F
  | .appFun E a, F => .appFun (compose E F) a
  | .proj b E, F => .proj b (compose E F)
  | .opLeft o E a, F => .opLeft o (compose E F) a
  | .opRight o n E, F => .opRight o n (compose E F)
  | .ite E t f, F => .ite (compose E F) t f

@[simp] theorem plug_compose (E F : EvalCtx) (e : Term) :
    plug (compose E F) e = plug E (plug F e) := by
  induction E generalizing F e <;> simp [compose, plug, *]

end EvalCtx

theorem step_plug (E : EvalCtx) {e e'} (h : Step e e') :
    Step (EvalCtx.plug E e) (EvalCtx.plug E e') := by
  rcases h with ⟨F, r, r', hRoot, he, he'⟩
  refine ⟨EvalCtx.compose E F, r, r', hRoot, ?_, ?_⟩
  · simpa [EvalCtx.plug_compose] using congrArg (EvalCtx.plug E) he
  · simpa [EvalCtx.plug_compose] using congrArg (EvalCtx.plug E) he'


def GoodDivergingInt (e : Term) : Prop :=
  Term.HasType [] e .int ∧ Term.Diverges e

theorem goodDivergingInt_step {e : Term} (hGood : GoodDivergingInt e) :
    ∃ e', Step e e' ∧ GoodDivergingInt e' := by
  rcases divergent_closed_int_can_step hGood.1 hGood.2 with ⟨e', hStep⟩
  exact ⟨e', hStep, step_hasType_closed hStep hGood.1,
    step_diverges_forward hGood.2 hStep⟩

noncomputable def nextGoodDivergingInt (x : {e : Term // GoodDivergingInt e}) :
    {e : Term // GoodDivergingInt e} :=
  ⟨Classical.choose (goodDivergingInt_step x.property),
    (Classical.choose_spec (goodDivergingInt_step x.property)).2⟩

theorem nextGoodDivergingInt_step (x : {e : Term // GoodDivergingInt e}) :
    Step x.val (nextGoodDivergingInt x).val :=
  (Classical.choose_spec (goodDivergingInt_step x.property)).1

noncomputable def goodDivergingIntRun (x : {e : Term // GoodDivergingInt e}) : Nat →
    {e : Term // GoodDivergingInt e}
  | 0 => x
  | n + 1 => nextGoodDivergingInt (goodDivergingIntRun x n)

theorem goodDivergingInt_infiniteSteps {e : Term} (hGood : GoodDivergingInt e) :
    InfiniteSteps e := by
  let x : {e : Term // GoodDivergingInt e} := ⟨e, hGood⟩
  refine ⟨fun n => (goodDivergingIntRun x n).val, rfl, ?_⟩
  intro n
  exact nextGoodDivergingInt_step (goodDivergingIntRun x n)


/-- Choose a successor while retaining reachability from the initial term. -/
noncomputable def reachableStepNext
    {e : Term}
    (hNext : ∀ {q}, Steps e q → ∃ q', Step q q')
    (x : {q : Term // Steps e q}) :
    {q : Term // Steps e q} :=
  ⟨Classical.choose (hNext x.property),
    Steps.tail x.property (Classical.choose_spec (hNext x.property))⟩

theorem reachableStepNext_step
    {e : Term}
    (hNext : ∀ {q}, Steps e q → ∃ q', Step q q')
    (x : {q : Term // Steps e q}) :
    Step x.val (reachableStepNext hNext x).val :=
  Classical.choose_spec (hNext x.property)

/-- An infinite run on reachable states. Every iteration is one actual
source-language Step, rather than a machine administration step. -/
noncomputable def reachableStepRun
    {e : Term}
    (hNext : ∀ {q}, Steps e q → ∃ q', Step q q')
    (x : {q : Term // Steps e q}) : Nat → {q : Term // Steps e q}
  | 0 => x
  | n + 1 => reachableStepNext hNext (reachableStepRun hNext x n)

/-- If every reachable state can step, the initial term has an infinite
CBN source reduction sequence. -/
theorem infiniteSteps_of_reachable_can_step
    {e : Term}
    (hNext : ∀ {q}, Steps e q → ∃ q', Step q q') :
    InfiniteSteps e := by
  let x : {q : Term // Steps e q} := ⟨e, Steps.refl⟩
  refine ⟨fun n => (reachableStepRun hNext x n).val, rfl, ?_⟩
  intro n
  exact reachableStepNext_step hNext (reachableStepRun hNext x n)

end Strictness
