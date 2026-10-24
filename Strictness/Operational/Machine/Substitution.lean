import Strictness.Operational.Machine.Readback

/-!
Simulation after replacing the open variable by a closed test term.

Transports closures and continuations through replacement, simulates finite
executions, and shows that a demanded variable becomes an observed error.
-/

namespace Strictness

/-- One inductive relation covers both closures and environments, avoiding a
separate mutually-recursive environment relation. -/
inductive ReplaceRel (a : Term) :
    Sum Closure (List (Option Closure)) → Sum Closure (List (Option Closure)) → Prop where
  | closure {e env env'} : ReplaceRel a (.inr env) (.inr env') →
      ReplaceRel a (.inl (.mk e env)) (.inl (.mk e env'))
  | envNil : ReplaceRel a (.inr []) (.inr [])
  | envNeutral {env env'} : ReplaceRel a (.inr env) (.inr env') →
      ReplaceRel a (.inr (none :: env)) (.inr (some (.mk a []) :: env'))
  | envClosure {c c' env env'} : ReplaceRel a (.inl c) (.inl c') →
      ReplaceRel a (.inr env) (.inr env') →
      ReplaceRel a (.inr (some c :: env)) (.inr (some c' :: env'))

abbrev ReplaceClosure (a : Term) (c c' : Closure) : Prop :=
  ReplaceRel a (.inl c) (.inl c')

abbrev ReplaceEnv (a : Term) (env env' : List (Option Closure)) : Prop :=
  ReplaceRel a (.inr env) (.inr env')

abbrev ErrRel := ReplaceRel .err

abbrev ErrClosure (c c' : Closure) : Prop := ErrRel (.inl c) (.inl c')

abbrev ErrEnv (env env' : List (Option Closure)) : Prop := ErrRel (.inr env) (.inr env')

theorem errEnv_lookup_neutral : ∀ {env env'}, ErrEnv env env' → ∀ i,
    Closure.lookup env i = some none →
      Closure.lookup env' i = some (some (.mk .err []))
  | _, _, .envNil, _, h => by simp [Closure.lookup] at h
  | _, _, .envNeutral hrel, 0, _ => rfl
  | _, _, .envNeutral hrel, i + 1, h => errEnv_lookup_neutral hrel i h
  | _, _, .envClosure hClosure hrel, 0, h => by simp [Closure.lookup] at h
  | _, _, .envClosure hClosure hrel, i + 1, h => errEnv_lookup_neutral hrel i h

/-- A delayed closure is transported pointwise by the replacement relation. -/
theorem replaceEnv_lookup_closure : ∀ {a env env'}, ReplaceEnv a env env' → ∀ i c,
    Closure.lookup env i = some (some c) →
      ∃ c', Closure.lookup env' i = some (some c') ∧ ReplaceClosure a c c'
  | _, _, _, .envNil, _, _, h => by simp [Closure.lookup] at h
  | _, _, _, .envNeutral hrel, 0, _, h => by simp [Closure.lookup] at h
  | _, _, _, .envNeutral hrel, i + 1, c, h => replaceEnv_lookup_closure hrel i c h
  | _, _, _, .envClosure hClosure hrel, 0, c, h => by
      simp [Closure.lookup] at h
      subst c
      exact ⟨_, rfl, hClosure⟩
  | _, _, _, .envClosure hClosure hrel, i + 1, c, h => replaceEnv_lookup_closure hrel i c h

inductive ReplaceKont (a : Term) : Kont → Kont → Prop where
  | app {c c'} : ReplaceClosure a c c' → ReplaceKont a (.app c) (.app c')
  | proj {b} : ReplaceKont a (.proj b) (.proj b)
  | opLeft (o : PrimOp) {c c'} : ReplaceClosure a c c' → ReplaceKont a (.opLeft o c) (.opLeft o c')
  | opRight (o : PrimOp) {n} : ReplaceKont a (.opRight o n) (.opRight o n)
  | ite {t f t' f'} : ReplaceClosure a t t' → ReplaceClosure a f f' →
      ReplaceKont a (.ite t f) (.ite t' f')

inductive ReplaceKonts (a : Term) : List Kont → List Kont → Prop where
  | nil : ReplaceKonts a [] []
  | cons {k k' ks ks'} : ReplaceKont a k k' → ReplaceKonts a ks ks' →
      ReplaceKonts a (k :: ks) (k' :: ks')

def ReplaceState (a : Term) (s s' : MachineState) : Prop :=
  ReplaceClosure a s.focus s'.focus ∧ ReplaceKonts a s.kont s'.kont

abbrev ErrKont := ReplaceKont .err
abbrev ErrKonts := ReplaceKonts .err
abbrev ErrState := ReplaceState .err

theorem demand_forces_error_step {i env env' k} (hEnv : ErrEnv env env')
    (hDemand : Closure.lookup env i = some none) :
    ∃ s', MachineStep ⟨.mk (.var i) env', k⟩ s' ∧ MachineState.IsError s' := by
  refine ⟨⟨.mk .err [], k⟩, ?_, by trivial⟩
  exact MachineStep.var (errEnv_lookup_neutral hEnv i hDemand)

/-- Replacing the open variable by any closed semantic test term commutes with
all non-demanding machine transitions. -/
theorem replace_step_simulation : ∀ {a c c' k k' t},
    ReplaceClosure a c c' → ReplaceKonts a k k' →
    MachineStep ⟨c, k⟩ t → ∃ t', MachineStep ⟨c', k'⟩ t' ∧ ReplaceState a t t'
  | _, _, _, _, _, _, hFocus, hKont, .var hLookup => by
      cases hFocus with
      | closure hEnv =>
        rcases replaceEnv_lookup_closure hEnv _ _ hLookup with ⟨c', hLookup', hc'⟩
        exact ⟨⟨c', _⟩, MachineStep.var hLookup', ⟨hc', hKont⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .app => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk _ _, .app (.mk _ _) :: _⟩, MachineStep.app,
          ⟨.closure hEnv, .cons (.app (.closure hEnv)) hKont⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .proj => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk _ _, .proj _ :: _⟩, MachineStep.proj,
          ⟨.closure hEnv, .cons .proj hKont⟩⟩
  | _, .mk (.op o e₁ e₂) env, _, _, _, _, hFocus, hKont, (.op .(o)) => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk _ _, .opLeft o (.mk _ _) :: _⟩, MachineStep.op o,
          ⟨.closure hEnv, .cons (.opLeft o (.closure hEnv)) hKont⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .ite => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk _ _, .ite (.mk _ _) (.mk _ _) :: _⟩, MachineStep.ite,
          ⟨.closure hEnv,
            .cons (.ite (.closure hEnv) (.closure hEnv)) hKont⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .letE => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk _ (some (.mk _ _) :: _), _⟩, MachineStep.letE,
          ⟨.closure (.envClosure (.closure hEnv) hEnv), hKont⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .fix => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk _ (some (.mk _ _) :: _), _⟩, MachineStep.fix,
          ⟨.closure (.envClosure (.closure hEnv) hEnv), hKont⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .lamApp => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hArg hRest =>
          cases hArg with
          | app hArg =>
            exact ⟨⟨.mk _ (some _ :: _), _⟩, MachineStep.lamApp,
              ⟨.closure (.envClosure hArg hEnv), hRest⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .projLeft => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hFrame hRest =>
          cases hFrame with
          | proj => exact ⟨⟨.mk _ _, _⟩, MachineStep.projLeft,
              ⟨.closure hEnv, hRest⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .projRight => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hFrame hRest =>
          cases hFrame with
          | proj => exact ⟨⟨.mk _ _, _⟩, MachineStep.projRight,
              ⟨.closure hEnv, hRest⟩⟩
  | _, .mk (.int n) env, _, .opLeft o arg :: k, _, _, hFocus, hKont, .opLeft .(o) => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hFrame hRest =>
          cases hFrame with
          | opLeft o hArg => exact ⟨⟨_, .opRight o _ :: _⟩, MachineStep.opLeft o,
              ⟨hArg, .cons (.opRight o) hRest⟩⟩
  | _, .mk (.int n₂) env, _, .opRight o n₁ :: k, _, _, hFocus, hKont, .opRight .(o) => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hFrame hRest =>
          cases hFrame with
          | opRight o => exact ⟨⟨.mk _ _, _⟩, MachineStep.opRight o,
              ⟨.closure hEnv, hRest⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .ifTrue hn => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hFrame hRest =>
          cases hFrame with
          | ite hThen hElse => exact ⟨⟨_, _⟩, MachineStep.ifTrue hn,
              ⟨hThen, hRest⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .ifFalse => by
      cases hFocus with
      | closure hEnv =>
        cases hKont with
        | cons hFrame hRest =>
          cases hFrame with
          | ite hThen hElse => exact ⟨⟨_, _⟩, MachineStep.ifFalse,
              ⟨hElse, hRest⟩⟩
  | _, _, _, _, _, _, hFocus, hKont, .omega => by
      cases hFocus with
      | closure hEnv =>
        exact ⟨⟨.mk .omega _, _⟩, MachineStep.omega,
          ⟨.closure hEnv, hKont⟩⟩

theorem replace_steps_simulation {a s t s'} (hRel : ReplaceState a s s')
    (hSteps : MachineSteps s t) :
    ∃ t', MachineSteps s' t' ∧ ReplaceState a t t' := by
  induction hSteps generalizing s' with
  | refl => exact ⟨s', .refl, hRel⟩
  | tail hSteps hStep ih =>
    rcases ih hRel with ⟨u', hu', hRelu⟩
    rcases hRelu with ⟨hFocus, hKont⟩
    rcases replace_step_simulation hFocus hKont hStep with ⟨t', hStep', hRelt⟩
    exact ⟨t', .tail hu' hStep', hRelt⟩

theorem initial_replace_state (a e : Term) :
    ReplaceState a (MachineState.open1 e) (MachineState.closed1 a e) := by
  exact ⟨.closure (.envNeutral .envNil), .nil⟩

theorem open_steps_replaced {a e s}
    (hSteps : MachineSteps (MachineState.open1 e) s) :
    ∃ s', MachineSteps (MachineState.closed1 a e) s' ∧ ReplaceState a s s' :=
  replace_steps_simulation (initial_replace_state a e) hSteps

theorem replace_returnsInt {a s s' n} (hRel : ReplaceState a s s')
    (hReturn : MachineState.ReturnsInt s n) : MachineState.ReturnsInt s' n := by
  rcases hReturn with ⟨env, rfl⟩
  rcases s' with ⟨focus', k'⟩
  rcases hRel with ⟨hFocus, hKont⟩
  cases hFocus with
  | closure hEnv =>
    cases hKont with
    | nil => exact ⟨_, rfl⟩

theorem replace_error {a s s'} (hRel : ReplaceState a s s')
    (hError : MachineState.IsError s) : MachineState.IsError s' := by
  rcases s with ⟨⟨e, env⟩, k⟩
  rcases s' with ⟨focus', k'⟩
  cases e <;> simp [MachineState.IsError] at hError
  cases hRel.1 with
  | closure hEnv => trivial

/-! ## Machine observations used in the source-reduction proof

These lemmas relate closure-machine runs to substitution tests and variable
demand. Source-language small-step consequences are proved in
`Strictness/Soundness/FiniteObservations.lean` and `Strictness/Soundness/Observational.lean`.
-/

/-- A finite open execution which reaches `E[x]` becomes a finite execution
of the `err` instantiation which reaches the machine error marker. -/
theorem demand_reaches_err_machine {e s}
    (hSteps : MachineSteps (MachineState.open1 e) s)
    (hDemand : MachineState.Demands s) :
    ∃ s', MachineSteps (MachineState.closed1 .err e) s' ∧ MachineState.IsError s' := by
  rcases replace_steps_simulation (initial_replace_state .err e) hSteps with
    ⟨s', hSteps', hRel⟩
  rcases s with ⟨⟨focusTerm, env⟩, k⟩
  rcases s' with ⟨focus', k'⟩
  cases focusTerm with
  | var i =>
    change Closure.lookup env i = some none at hDemand
    cases hRel.1 with
    | closure hEnv =>
      rcases demand_forces_error_step hEnv hDemand with ⟨s'', hStep, hError⟩
      exact ⟨s'', .tail hSteps' hStep, hError⟩
  | int n => simp [MachineState.Demands] at hDemand
  | lam body => simp [MachineState.Demands] at hDemand
  | fix body => simp [MachineState.Demands] at hDemand
  | app e₁ e₂ => simp [MachineState.Demands] at hDemand
  | pair e₁ e₂ => simp [MachineState.Demands] at hDemand
  | proj b e => simp [MachineState.Demands] at hDemand
  | op o e₁ e₂ => simp [MachineState.Demands] at hDemand
  | ite e₀ e₁ e₂ => simp [MachineState.Demands] at hDemand
  | letE e₁ e₂ => simp [MachineState.Demands] at hDemand
  | omega => simp [MachineState.Demands] at hDemand
  | err => simp [MachineState.Demands] at hDemand

end Strictness
