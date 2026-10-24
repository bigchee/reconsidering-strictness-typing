import Strictness.Operational.Machine.Typing

/-!
Readback from closed closure-machine states to source terms.

Each machine transition is administrative or induces a source transition.
Finite machine executions ending in an error or an integer therefore give
the corresponding big-step observation.
-/

namespace Strictness

/-- Relational readback of a closure environment containing only closed
delayed computations.  The tail substitution is intentionally arbitrary: it
represents variables outside the lexical environment, which cannot occur in
a well-scoped source program. -/
inductive ReadRel :
    Sum Closure (List (Option Closure)) → Sum Term Substitution → Prop where
  | closure {e env ρ} : ReadRel (.inr env) (.inr ρ) →
      ReadRel (.inl (.mk e env)) (.inl (Substitution.apply ρ e))
  | envNil {ρ} (hρ : ∀ i, Term.Closed (ρ i)) :
      ReadRel (.inr []) (.inr ρ)
  | envSome {c q env ρ} :
      ReadRel (.inl c) (.inl q) → Term.Closed q →
      ReadRel (.inr env) (.inr ρ) →
      ReadRel (.inr (some c :: env)) (.inr (Substitution.extend ρ q))

abbrev ReadsClosure (c : Closure) (q : Term) : Prop := ReadRel (.inl c) (.inl q)

abbrev ReadsEnv (env : List (Option Closure)) (ρ : Substitution) : Prop :=
  ReadRel (.inr env) (.inr ρ)

inductive ReadKont : Kont → EvalCtx → Prop where
  | app {a q} : ReadsClosure a q → ReadKont (.app a) (.appFun .hole q)
  | proj {b} : ReadKont (.proj b) (.proj b .hole)
  | opLeft (o : PrimOp) {a q} : ReadsClosure a q → ReadKont (.opLeft o a) (.opLeft o .hole q)
  | opRight (o : PrimOp) {n} : ReadKont (.opRight o n) (.opRight o n .hole)
  | ite {t f t' f'} : ReadsClosure t t' → ReadsClosure f f' →
      ReadKont (.ite t f) (.ite .hole t' f')

inductive ReadKonts : List Kont → EvalCtx → Prop where
  | nil : ReadKonts [] .hole
  | cons {k ks F E} : ReadKont k F → ReadKonts ks E →
      ReadKonts (k :: ks) (EvalCtx.compose E F)

def ReadsState (s : MachineState) (q : Term) : Prop :=
  ∃ focus E, ReadsClosure s.focus focus ∧ ReadKonts s.kont E ∧ q = EvalCtx.plug E focus

theorem reads_error_evalErr {s q} (hReads : ReadsState s q)
    (hError : MachineState.IsError s) : EvalErr q := by
  rcases s with ⟨⟨e, env⟩, k⟩
  cases e <;> simp [MachineState.IsError] at hError
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    subst q
    simp [Substitution.apply, Substitution.applyAt, EvalCtx.plug_err_evalErr]

theorem reads_closed_initial (a e : Term) (ha : Term.Closed a) :
    ReadsState (MachineState.closed1 a e) (Substitution.apply (singleSubst a) e) := by
  have hBase : ReadsEnv [] (singleSubst a) :=
    .envNil (by intro i; exact ha)
  have hArg : ReadsClosure (.mk a []) a := by
    have hArgRaw : ReadsClosure (.mk a []) (Substitution.apply (singleSubst a) a) :=
      .closure hBase
    simpa [substitution_apply_eq_of_closed (singleSubst a) ha] using hArgRaw
  have hEnv : ReadsEnv [some (.mk a [])] (Substitution.extend (singleSubst a) a) :=
    .envSome hArg ha hBase
  have hExtend : Substitution.extend (singleSubst a) a = singleSubst a := by
    funext i
    cases i with
    | zero => simp [Substitution.extend, singleSubst]
    | succ i => simp [Substitution.extend, singleSubst, Term.shift_eq_of_closed ha]
  rw [← hExtend]
  exact ⟨_, .hole, .closure hEnv, .nil, rfl⟩

theorem readsEnv_closed : ∀ {env ρ}, ReadsEnv env ρ → ∀ i, Term.Closed (ρ i)
  | _, _, .envNil hρ => hρ
  | _, _, .envSome _ hq hEnv =>
      Substitution.extend_closed _ _ (readsEnv_closed hEnv) hq

theorem readsClosure_closed {c q} (h : ReadsClosure c q) : Term.Closed q := by
  cases h with
  | closure hEnv => exact apply_closed_of_closed_images _ (readsEnv_closed hEnv) _

theorem readsEnv_lookup_closure : ∀ {env ρ}, ReadsEnv env ρ → ∀ i c,
    Closure.lookup env i = some (some c) → ∃ q, ReadsClosure c q ∧ ρ i = q
  | _, _, .envNil _, _, _, h => by simp [Closure.lookup] at h
  | _, _, .envSome hHead hq hTail, 0, c, h => by
      simp [Closure.lookup] at h
      subst c
      exact ⟨_, hHead, rfl⟩
  | _, _, .envSome hHead hq hTail, i + 1, c, h => by
      rcases readsEnv_lookup_closure hTail i c h with ⟨q, hc, hq'⟩
      exact ⟨q, hc, by
        simpa [Substitution.extend, Term.shift_eq_of_closed (readsClosure_closed hc)]
          using congrArg (Term.shift 1 0) hq'⟩

theorem reads_app_states {e₁ e₂ env ρ k E}
    (hEnv : ReadsEnv env ρ) (hKont : ReadKonts k E) :
    ReadsState ⟨.mk (.app e₁ e₂) env, k⟩
      (EvalCtx.plug E (.app (Substitution.apply ρ e₁) (Substitution.apply ρ e₂))) ∧
    ReadsState ⟨.mk e₁ env, .app (.mk e₂ env) :: k⟩
      (EvalCtx.plug E (.app (Substitution.apply ρ e₁) (Substitution.apply ρ e₂))) := by
  constructor
  · exact ⟨_, E, .closure hEnv, hKont, rfl⟩
  · exact ⟨_, EvalCtx.compose E (.appFun .hole (Substitution.apply ρ e₂)),
      .closure hEnv, .cons (.app (.closure hEnv)) hKont, by
        simp [EvalCtx.plug_compose, EvalCtx.plug]⟩

theorem machine_app_readback {e₁ e₂ env k q}
    (hReads : ReadsState ⟨.mk (.app e₁ e₂) env, k⟩ q) :
    ∃ q', ReadsState ⟨.mk e₁ env, .app (.mk e₂ env) :: k⟩ q' ∧ q = q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rcases reads_app_states hEnv hKont with ⟨_, hNext⟩
    exact ⟨_, hNext, hq⟩

theorem machine_lamApp_readback {body env a k q}
    (hReads : ReadsState ⟨.mk (.lam body) env, .app a :: k⟩ q) :
    ∃ q', ReadsState ⟨.mk body (some a :: env), k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | app hArg =>
        rename_i ρ E qa
        have hqa : Term.Closed qa := readsClosure_closed hArg
        have hClosedρ : ∀ i, Term.Closed (ρ i) := readsEnv_closed hEnv
        have hBody : ReadsClosure (.mk body (some a :: env))
            (Substitution.apply (Substitution.extend ρ qa) body) :=
          .closure (.envSome hArg hqa hEnv)
        refine ⟨EvalCtx.plug _ (Substitution.apply (Substitution.extend ρ qa) body),
          ⟨_, _, hBody, hRest, rfl⟩, ?_⟩
        rw [hq]
        have hBeta : Step (.app (.lam (Substitution.applyAt ρ 1 body)) qa)
            (Substitution.apply (Substitution.extend ρ qa) body) := by
          rw [Substitution.apply_extend_eq_instantiate_of_closed ρ qa body hClosedρ hqa]
          exact ⟨.hole, _, _, .beta, rfl, rfl⟩
        simpa [EvalCtx.plug_compose, EvalCtx.plug] using step_plug E hBeta

theorem machine_let_readback {e₁ e₂ env k q}
    (hReads : ReadsState ⟨.mk (.letE e₁ e₂) env, k⟩ q) :
    ∃ q', ReadsState ⟨.mk e₂ (some (.mk e₁ env) :: env), k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    have hClosedρ : ∀ i, Term.Closed (ρ i) := readsEnv_closed hEnv
    let q₁ := Substitution.apply ρ e₁
    have hq₁ : Term.Closed q₁ := apply_closed_of_closed_images _ hClosedρ _
    have hDelayed : ReadsClosure (.mk e₁ env) q₁ := .closure hEnv
    have hBody : ReadsClosure (.mk e₂ (some (.mk e₁ env) :: env))
        (Substitution.apply (Substitution.extend ρ q₁) e₂) :=
      .closure (.envSome hDelayed hq₁ hEnv)
    refine ⟨EvalCtx.plug E (Substitution.apply (Substitution.extend ρ q₁) e₂),
      ⟨_, E, hBody, hKont, rfl⟩, ?_⟩
    rw [hq]
    have hLet : Step (.letE q₁ (Substitution.applyAt ρ 1 e₂))
        (Substitution.apply (Substitution.extend ρ q₁) e₂) := by
      rw [Substitution.apply_extend_eq_instantiate_of_closed ρ q₁ e₂ hClosedρ hq₁]
      exact ⟨.hole, _, _, .letE, rfl, rfl⟩
    simpa [q₁, EvalCtx.plug] using step_plug E hLet

/-- Unfolding a fix closure agrees with one source-level fix step. -/
theorem machine_fix_readback {body env k q}
    (hReads : ReadsState ⟨.mk (.fix body) env, k⟩ q) :
    ∃ q', ReadsState
      ⟨.mk body (some (.mk (.fix body) env) :: env), k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    have hClosedρ : ∀ i, Term.Closed (ρ i) := readsEnv_closed hEnv
    let qSelf := Substitution.apply ρ (.fix body)
    have hSelfClosed : Term.Closed qSelf :=
      apply_closed_of_closed_images ρ hClosedρ (.fix body)
    have hSelf : ReadsClosure (.mk (.fix body) env) qSelf := .closure hEnv
    have hBody : ReadsClosure
        (.mk body (some (.mk (.fix body) env) :: env))
        (Substitution.apply (Substitution.extend ρ qSelf) body) :=
      .closure (.envSome hSelf hSelfClosed hEnv)
    refine ⟨EvalCtx.plug E
      (Substitution.apply (Substitution.extend ρ qSelf) body),
      ⟨_, E, hBody, hKont, rfl⟩, ?_⟩
    rw [hq]
    have hFix : Step (.fix (Substitution.applyAt ρ 1 body))
        (Substitution.apply (Substitution.extend ρ qSelf) body) := by
      rw [Substitution.apply_extend_eq_instantiate_of_closed
        ρ qSelf body hClosedρ hSelfClosed]
      exact ⟨.hole, _, _, RootStep.fix, rfl, rfl⟩
    simpa only [qSelf, Substitution.apply_fix] using step_plug E hFix

theorem machine_proj_readback {b e env k q}
    (hReads : ReadsState ⟨.mk (.proj b e) env, k⟩ q) :
    ∃ q', ReadsState ⟨.mk e env, .proj b :: k⟩ q' ∧ q = q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    refine ⟨EvalCtx.plug E (.proj b (Substitution.apply ρ e)),
      ⟨_, EvalCtx.compose E (.proj b .hole), .closure hEnv,
        .cons .proj hKont, ?_⟩, hq⟩
    simp [EvalCtx.plug_compose, EvalCtx.plug]

theorem machine_projLeft_readback {e₁ e₂ env k q}
    (hReads : ReadsState ⟨.mk (.pair e₁ e₂) env, .proj true :: k⟩ q) :
    ∃ q', ReadsState ⟨.mk e₁ env, k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | proj =>
        refine ⟨EvalCtx.plug _ (Substitution.apply ρ e₁),
          ⟨_, _, .closure hEnv, hRest, rfl⟩, ?_⟩
        rw [hq]
        have hRoot : Step (.proj true (.pair (Substitution.apply ρ e₁)
            (Substitution.apply ρ e₂))) (Substitution.apply ρ e₁) :=
          ⟨.hole, _, _, .projLeft, rfl, rfl⟩
        simpa [EvalCtx.plug_compose, EvalCtx.plug] using step_plug _ hRoot

theorem machine_projRight_readback {e₁ e₂ env k q}
    (hReads : ReadsState ⟨.mk (.pair e₁ e₂) env, .proj false :: k⟩ q) :
    ∃ q', ReadsState ⟨.mk e₂ env, k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | proj =>
        refine ⟨EvalCtx.plug _ (Substitution.apply ρ e₂),
          ⟨_, _, .closure hEnv, hRest, rfl⟩, ?_⟩
        rw [hq]
        have hRoot : Step (.proj false (.pair (Substitution.apply ρ e₁)
            (Substitution.apply ρ e₂))) (Substitution.apply ρ e₂) :=
          ⟨.hole, _, _, .projRight, rfl, rfl⟩
        simpa [EvalCtx.plug_compose, EvalCtx.plug] using step_plug _ hRoot

theorem machine_op_readback {e₁ e₂ env k q}
    (hReads : ReadsState ⟨.mk (.op o e₁ e₂) env, k⟩ q) :
    ∃ q', ReadsState ⟨.mk e₁ env, .opLeft o (.mk e₂ env) :: k⟩ q' ∧ q = q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    refine ⟨EvalCtx.plug E (.op o (Substitution.apply ρ e₁) (Substitution.apply ρ e₂)),
      ⟨_, EvalCtx.compose E (.opLeft o .hole (Substitution.apply ρ e₂)), .closure hEnv,
        .cons (.opLeft o (.closure hEnv)) hKont, ?_⟩, hq⟩
    simp [EvalCtx.plug_compose, EvalCtx.plug]

theorem machine_opLeft_readback {n env a k q}
    (hReads : ReadsState ⟨.mk (.int n) env, .opLeft o a :: k⟩ q) :
    ∃ q', ReadsState ⟨a, .opRight o n :: k⟩ q' ∧ q = q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | opLeft o hArg =>
        rename_i E qa
        refine ⟨EvalCtx.plug E (.op o (.int n) qa),
          ⟨_, EvalCtx.compose E (.opRight o n .hole), hArg,
            .cons (.opRight o) hRest, ?_⟩, ?_⟩
        simp [EvalCtx.plug_compose, EvalCtx.plug]
        simpa [Substitution.apply, Substitution.applyAt,
          EvalCtx.plug_compose, EvalCtx.plug] using hq

theorem machine_opRight_readback {n₁ n₂ env k q}
    (hReads : ReadsState ⟨.mk (.int n₂) env, .opRight o n₁ :: k⟩ q) :
    ∃ q', ReadsState ⟨.mk (.int (o.eval n₁ n₂)) env, k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | opRight o =>
        refine ⟨EvalCtx.plug _ (.int (o.eval n₁ n₂)),
          ⟨_, _, .closure hEnv, hRest, rfl⟩, ?_⟩
        rw [hq]
        have hRoot : Step (.op o (.int n₁) (.int n₂)) (.int (o.eval n₁ n₂)) :=
          ⟨.hole, _, _, .op o, rfl, rfl⟩
        simpa [EvalCtx.plug_compose, EvalCtx.plug] using step_plug _ hRoot

theorem machine_ite_readback {e₀ e₁ e₂ env k q}
    (hReads : ReadsState ⟨.mk (.ite e₀ e₁ e₂) env, k⟩ q) :
    ∃ q', ReadsState ⟨.mk e₀ env, .ite (.mk e₁ env) (.mk e₂ env) :: k⟩ q' ∧ q = q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    refine ⟨EvalCtx.plug E (.ite (Substitution.apply ρ e₀)
        (Substitution.apply ρ e₁) (Substitution.apply ρ e₂)),
      ⟨_, EvalCtx.compose E (.ite .hole (Substitution.apply ρ e₁)
          (Substitution.apply ρ e₂)), .closure hEnv,
        .cons (.ite (.closure hEnv) (.closure hEnv)) hKont, ?_⟩, hq⟩
    simp [EvalCtx.plug_compose, EvalCtx.plug]

theorem machine_ifTrue_readback {n t f env k q} (hn : n ≠ 0)
    (hReads : ReadsState ⟨.mk (.int n) env, .ite t f :: k⟩ q) :
    ∃ q', ReadsState ⟨t, k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | ite hThen hElse =>
        rename_i E qt qf
        refine ⟨EvalCtx.plug E qt, ⟨_, E, hThen, hRest, rfl⟩, ?_⟩
        rw [hq]
        have hRoot : Step (.ite (.int n) qt qf) qt :=
          ⟨.hole, _, _, .ifTrue hn, rfl, rfl⟩
        simpa [EvalCtx.plug_compose, EvalCtx.plug, Substitution.apply,
          Substitution.applyAt] using step_plug E hRoot

theorem machine_ifFalse_readback {t f env k q}
    (hReads : ReadsState ⟨.mk (.int 0) env, .ite t f :: k⟩ q) :
    ∃ q', ReadsState ⟨f, k⟩ q' ∧ Step q q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    cases hKont with
    | cons hFrame hRest =>
      cases hFrame with
      | ite hThen hElse =>
        rename_i E qt qf
        refine ⟨EvalCtx.plug E qf, ⟨_, E, hElse, hRest, rfl⟩, ?_⟩
        rw [hq]
        have hRoot : Step (.ite (.int 0) qt qf) qf :=
          ⟨.hole, _, _, .ifFalse, rfl, rfl⟩
        simpa [EvalCtx.plug_compose, EvalCtx.plug, Substitution.apply,
          Substitution.applyAt] using step_plug E hRoot

theorem machine_var_readback {i env c k q}
    (hLookup : Closure.lookup env i = some (some c))
    (hReads : ReadsState ⟨.mk (.var i) env, k⟩ q) :
    ∃ q', ReadsState ⟨c, k⟩ q' ∧ q = q' := by
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    rename_i ρ
    rcases readsEnv_lookup_closure hEnv i c hLookup with ⟨qc, hc, hρ⟩
    refine ⟨EvalCtx.plug E qc, ⟨qc, E, hc, hKont, rfl⟩, ?_⟩
    simpa [Substitution.apply, Substitution.applyAt, hρ] using hq

/-- Every closure-machine transition is either administrative after readback,
or one primitive source reduction under the reconstructed evaluation context. -/
theorem machine_step_readback : ∀ {c k t q}, ReadsState ⟨c, k⟩ q →
    MachineStep ⟨c, k⟩ t → ∃ q', ReadsState t q' ∧ (q = q' ∨ Step q q')
  | _, _, _, _, hReads, .var hLookup => by
      rcases machine_var_readback hLookup hReads with ⟨q', hq', hEq⟩
      exact ⟨q', hq', .inl hEq⟩
  | _, _, _, _, hReads, .app => by
      rcases machine_app_readback hReads with ⟨q', hq', hEq⟩
      exact ⟨q', hq', .inl hEq⟩
  | _, _, _, _, hReads, .proj => by
      rcases machine_proj_readback hReads with ⟨q', hq', hEq⟩
      exact ⟨q', hq', .inl hEq⟩
  | .mk (.op o e₁ e₂) env, _, _, _, hReads, (.op .(o)) => by
      rcases machine_op_readback hReads with ⟨q', hq', hEq⟩
      exact ⟨q', hq', .inl hEq⟩
  | _, _, _, _, hReads, .ite => by
      rcases machine_ite_readback hReads with ⟨q', hq', hEq⟩
      exact ⟨q', hq', .inl hEq⟩
  | _, _, _, _, hReads, .letE => by
      rcases machine_let_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .fix => by
      rcases machine_fix_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .lamApp => by
      rcases machine_lamApp_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .projLeft => by
      rcases machine_projLeft_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .projRight => by
      rcases machine_projRight_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | .mk (.int n) env, .opLeft o arg :: k, _, _, hReads, .opLeft .(o) => by
      rcases machine_opLeft_readback hReads with ⟨q', hq', hEq⟩
      exact ⟨q', hq', .inl hEq⟩
  | .mk (.int n₂) env, .opRight o n₁ :: k, _, _, hReads, .opRight .(o) => by
      rcases machine_opRight_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .ifTrue hn => by
      rcases machine_ifTrue_readback hn hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .ifFalse => by
      rcases machine_ifFalse_readback hReads with ⟨q', hq', hStep⟩
      exact ⟨q', hq', .inr hStep⟩
  | _, _, _, _, hReads, .omega => by
      rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
      cases hFocus with
      | closure hEnv =>
        refine ⟨_, ⟨_, E, .closure hEnv, hKont, rfl⟩, .inr ?_⟩
        rw [hq]
        have hRoot : Step (.omega : Term) .omega :=
          ⟨.hole, .omega, .omega, .omega, rfl, rfl⟩
        simpa [Substitution.apply, Substitution.applyAt] using step_plug E hRoot

theorem machine_steps_readback {s t q} (hReads : ReadsState s q)
    (hSteps : MachineSteps s t) :
    ∃ q', ReadsState t q' ∧ Steps q q' := by
  induction hSteps generalizing q with
  | refl => exact ⟨q, hReads, .refl⟩
  | tail hSteps hStep ih =>
    rcases ih hReads with ⟨qMid, hMid, hPrefix⟩
    rcases machine_step_readback hMid hStep with ⟨qNext, hNext, hMove⟩
    cases hMove with
    | inl hEq =>
      subst qNext
      exact ⟨qMid, hNext, hPrefix⟩
    | inr hOne => exact ⟨qNext, hNext, .tail hPrefix hOne⟩

/-- Adequacy for the error observation: any finite closure-machine execution
ending at `err` gives the established big-step `EvalErr` observation. -/
theorem machine_error_implies_evalErr {a e s} (ha : Term.Closed a)
    (hSteps : MachineSteps (MachineState.closed1 a e) s)
    (hError : MachineState.IsError s) :
    EvalErr (Substitution.apply (singleSubst a) e) := by
  rcases machine_steps_readback (reads_closed_initial a e ha) hSteps with
    ⟨qEnd, hReadEnd, hReduce⟩
  exact steps_evalErr hReduce (reads_error_evalErr hReadEnd hError)


theorem reads_returnsInt_eval {s q n} (hReads : ReadsState s q)
    (hReturn : MachineState.ReturnsInt s n) : Eval q (.int n) := by
  rcases hReturn with ⟨env, rfl⟩
  rcases hReads with ⟨focus, E, hFocus, hKont, hq⟩
  cases hFocus with
  | closure hEnv =>
    cases hKont with
    | nil =>
      subst q
      exact Eval.int

theorem machine_return_int_implies_eval {a e s n} (ha : Term.Closed a)
    (hSteps : MachineSteps (MachineState.closed1 a e) s)
    (hReturn : MachineState.ReturnsInt s n) :
    Eval (Substitution.apply (singleSubst a) e) (.int n) := by
  rcases machine_steps_readback (reads_closed_initial a e ha) hSteps with
    ⟨qEnd, hReadEnd, hReduce⟩
  exact steps_eval hReduce (reads_returnsInt_eval hReadEnd hReturn)

end Strictness
