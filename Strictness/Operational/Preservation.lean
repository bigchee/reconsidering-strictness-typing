import Strictness.Language.SimpleInstantiation
import Strictness.Operational.SmallStepSubstitution

namespace Strictness

/-- Primitive CBN contractions preserve simple typing in any context. -/
theorem rootStep_hasType_open
    {Γ : Term.Ctx} {r r' : Term} {τ : SimpleTy}
    (hRoot : RootStep r r') (hType : Term.HasType Γ r τ) :
    Term.HasType Γ r' τ := by
  cases hRoot with
  | beta =>
      cases hType with
      | app hFun hArg =>
          cases hFun with
          | lam hBody =>
              exact hasType_instantiate_open hBody hArg
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
      | op o hLeft hRight => exact Term.HasType.int
  | ifTrue hn =>
      cases hType with
      | ite hCond hThen hElse => exact hThen
  | ifFalse =>
      cases hType with
      | ite hCond hThen hElse => exact hElse
  | letE =>
      cases hType with
      | letE hDef hBody =>
          exact hasType_instantiate_open hBody hDef
  | fix =>
      cases hType with
      | fix hBody =>
          exact hasType_instantiate_open hBody (Term.HasType.fix hBody)
  | omega =>
      exact hType

/-- Primitive contractions inside an evaluation context preserve typing. -/
theorem rootStep_context_hasType_open
    (E : EvalCtx) {Γ : Term.Ctx} {r r' : Term} {τ : SimpleTy}
    (hRoot : RootStep r r')
    (hType : Term.HasType Γ (EvalCtx.plug E r) τ) :
    Term.HasType Γ (EvalCtx.plug E r') τ := by
  induction E generalizing r r' τ with
  | hole =>
      exact rootStep_hasType_open hRoot hType
  | appFun E a ih =>
      cases hType with
      | app hFun hArg =>
          exact Term.HasType.app (ih hRoot hFun) hArg
  | proj b E ih =>
      cases b with
      | false =>
          cases hType with
          | projRight hPair =>
              exact Term.HasType.projRight (ih hRoot hPair)
      | true =>
          cases hType with
          | projLeft hPair =>
              exact Term.HasType.projLeft (ih hRoot hPair)
  | opLeft o E a ih =>
      cases hType with
      | op o hLeft hRight =>
          exact Term.HasType.op o (ih hRoot hLeft) hRight
  | opRight o n E ih =>
      cases hType with
      | op o hLeft hRight =>
          exact Term.HasType.op o hLeft (ih hRoot hRight)
  | ite E t f ih =>
      cases hType with
      | ite hCond hThen hElse =>
          exact Term.HasType.ite (ih hRoot hCond) hThen hElse

/-- One open-term CBN step preserves simple typing. -/
theorem step_hasType_open
    {Γ : Term.Ctx} {e e' : Term} {τ : SimpleTy}
    (hStep : Step e e') (hType : Term.HasType Γ e τ) :
    Term.HasType Γ e' τ := by
  rcases hStep with ⟨E, r, r', hRoot, rfl, rfl⟩
  exact rootStep_context_hasType_open E hRoot hType

/-- Every finite open-term CBN reduction prefix preserves simple typing. -/
theorem steps_hasType_open
    {Γ : Term.Ctx} {e q : Term} {τ : SimpleTy}
    (hSteps : Steps e q) (hType : Term.HasType Γ e τ) :
    Term.HasType Γ q τ := by
  induction hSteps generalizing τ with
  | refl =>
      exact hType
  | tail hSteps hStep ih =>
      exact step_hasType_open hStep (ih hType)

end Strictness
