import Strictness.Operational.Machine.Basic

/-!
Scope and typing invariants of the closure machine.

Proves preservation of lexical scope and simple typing and characterizes
terminal well-typed machine states. It does not use semantic soundness.
-/

namespace Strictness

/-- Lexical well-scoping for closures and recursively stored delayed
environments.  `none` is allowed and represents the original open variable. -/
inductive ScopeRel : Sum Closure (List (Option Closure)) → Prop where
  | closure {e env} : Term.ClosedAt env.length e → ScopeRel (.inr env) →
      ScopeRel (.inl (.mk e env))
  | envNil : ScopeRel (.inr [])
  | envNone {env} : ScopeRel (.inr env) → ScopeRel (.inr (none :: env))
  | envSome {c env} : ScopeRel (.inl c) → ScopeRel (.inr env) →
      ScopeRel (.inr (some c :: env))

abbrev ScopedClosure (c : Closure) : Prop := ScopeRel (.inl c)
abbrev ScopedEnv (env : List (Option Closure)) : Prop := ScopeRel (.inr env)

inductive ScopedKont : Kont → Prop where
  | app {a} : ScopedClosure a → ScopedKont (.app a)
  | proj {b} : ScopedKont (.proj b)
  | opLeft (o : PrimOp) {a} : ScopedClosure a → ScopedKont (.opLeft o a)
  | opRight (o : PrimOp) {n} : ScopedKont (.opRight o n)
  | ite {t f} : ScopedClosure t → ScopedClosure f → ScopedKont (.ite t f)

inductive ScopedKonts : List Kont → Prop where
  | nil : ScopedKonts []
  | cons {k ks} : ScopedKont k → ScopedKonts ks → ScopedKonts (k :: ks)

def ScopedState (s : MachineState) : Prop := ScopedClosure s.focus ∧ ScopedKonts s.kont

theorem scopedEnv_lookup_some : ∀ {env}, ScopedEnv env → ∀ i,
    i < env.length → ∃ entry, Closure.lookup env i = some entry
  | _, .envNil, _, h => by simp at h
  | _, .envNone hEnv, 0, _ => by exact ⟨none, rfl⟩
  | _, .envNone hEnv, i + 1, h => by
      simp only [List.length_cons] at h
      exact scopedEnv_lookup_some hEnv i (Nat.lt_of_succ_lt_succ h)
  | _, .envSome hClosure hEnv, 0, _ => by exact ⟨some _, rfl⟩
  | _, .envSome hClosure hEnv, i + 1, h => by
      simp only [List.length_cons] at h
      exact scopedEnv_lookup_some hEnv i (Nat.lt_of_succ_lt_succ h)

theorem scopedEnv_lookup_closure : ∀ {env}, ScopedEnv env → ∀ i c,
    Closure.lookup env i = some (some c) → ScopedClosure c
  | _, .envNil, _, _, h => by simp [Closure.lookup] at h
  | _, .envNone hEnv, 0, _, h => by simp [Closure.lookup] at h
  | _, .envNone hEnv, i + 1, c, h => scopedEnv_lookup_closure hEnv i c h
  | _, .envSome hClosure hEnv, 0, c, h => by
      simp [Closure.lookup] at h
      subst c
      exact hClosure
  | _, .envSome hClosure hEnv, i + 1, c, h => scopedEnv_lookup_closure hEnv i c h

/-- The machine never creates an out-of-scope closure or continuation. -/
theorem scoped_step : ∀ {c k t}, ScopedClosure c → ScopedKonts k →
    MachineStep ⟨c, k⟩ t → ScopedState t
  | _, _, _, .closure hTerm hEnv, hKont, .var hLookup =>
      ⟨scopedEnv_lookup_closure hEnv _ _ hLookup, hKont⟩
  | _, _, _, .closure hTerm hEnv, hKont, .app =>
      ⟨.closure hTerm.1 hEnv, .cons (.app (.closure hTerm.2 hEnv)) hKont⟩
  | _, _, _, .closure hTerm hEnv, hKont, .proj =>
      ⟨.closure hTerm hEnv, .cons .proj hKont⟩
  | .mk (.op o e₁ e₂) env, _, _, .closure hTerm hEnv, hKont, (.op .(o)) =>
      ⟨.closure hTerm.1 hEnv, .cons (.opLeft o (.closure hTerm.2 hEnv)) hKont⟩
  | _, _, _, .closure hTerm hEnv, hKont, .ite =>
      ⟨.closure hTerm.1 hEnv,
        .cons (.ite (.closure hTerm.2.1 hEnv) (.closure hTerm.2.2 hEnv)) hKont⟩
  | _, _, _, .closure hTerm hEnv, hKont, .letE =>
      ⟨.closure hTerm.2 (.envSome (.closure hTerm.1 hEnv) hEnv), hKont⟩
  | _, _, _, .closure hTerm hEnv, hKont, .fix =>
      ⟨.closure hTerm (.envSome (.closure hTerm hEnv) hEnv), hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons (.app hArg) hKont, .lamApp =>
      ⟨.closure hTerm (.envSome hArg hEnv), hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons .proj hKont, .projLeft =>
      ⟨.closure hTerm.1 hEnv, hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons .proj hKont, .projRight =>
      ⟨.closure hTerm.2 hEnv, hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons (.opLeft o hArg) hKont, .opLeft .(o) =>
      ⟨hArg, .cons (.opRight o) hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons (.opRight o) hKont, .opRight .(o) =>
      ⟨.closure (by trivial) hEnv, hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons (.ite hThen hElse) hKont, .ifTrue hn =>
      ⟨hThen, hKont⟩
  | _, _, _, .closure hTerm hEnv, .cons (.ite hThen hElse) hKont, .ifFalse =>
      ⟨hElse, hKont⟩
  | _, _, _, .closure hTerm hEnv, hKont, .omega =>
      ⟨.closure hTerm hEnv, hKont⟩

theorem scoped_steps {s t : MachineState} (hScope : ScopedState s)
    (hSteps : MachineSteps s t) : ScopedState t := by
  induction hSteps with
  | refl => exact hScope
  | tail hSteps hStep ih => exact scoped_step ih.1 ih.2 hStep

theorem initial_scoped_state {e : Term} (hScope : Term.ClosedAt 1 e) :
    ScopedState (MachineState.open1 e) :=
  ⟨.closure hScope (.envNone .envNil), .nil⟩

/-- A closure carries a typing derivation for its code, and every variable
which that derivation can mention has an environment entry.  Resolved entries
recursively carry the corresponding type; unresolved entries are precisely
the single open-variable observations. -/
inductive ClosureTyping : Closure → SimpleTy → Prop where
  | mk {e env Γ τ} : Term.HasType Γ e τ →
      (∀ {i σ}, Term.lookup Γ i = some σ →
        ∃ entry, Closure.lookup env i = some entry) →
      (∀ {i σ c}, Term.lookup Γ i = some σ →
        Closure.lookup env i = some (some c) → ClosureTyping c σ) →
      ClosureTyping (.mk e env) τ

inductive TypedKont : Kont → SimpleTy → SimpleTy → Prop where
  | app {a σ τ} : ClosureTyping a σ → TypedKont (.app a) (.arrow σ τ) τ
  | projLeft {σ τ} : TypedKont (.proj true) (.prod σ τ) σ
  | projRight {σ τ} : TypedKont (.proj false) (.prod σ τ) τ
  | opLeft (o : PrimOp) {a} : ClosureTyping a .int → TypedKont (.opLeft o a) .int .int
  | opRight (o : PrimOp) {n} : TypedKont (.opRight o n) .int .int
  | ite {t f τ} : ClosureTyping t τ → ClosureTyping f τ →
      TypedKont (.ite t f) .int τ

inductive TypedKonts : List Kont → SimpleTy → SimpleTy → Prop where
  | nil {τ} : TypedKonts [] τ τ
  | cons {k ks σ τ υ} : TypedKont k σ τ → TypedKonts ks τ υ →
      TypedKonts (k :: ks) σ υ

def TypedState (s : MachineState) (τ : SimpleTy) : Prop :=
  ∃ σ, ClosureTyping s.focus σ ∧ TypedKonts s.kont σ τ

theorem initial_typed_state {σ : SimpleTy} {e : Term}
    (hType : Term.HasType [σ] e .int) :
    TypedState (MachineState.open1 e) .int :=
  ⟨.int, .mk hType (by
      intro i τ hLookup
      cases i with
      | zero => exact ⟨none, rfl⟩
      | succ i => simp [Term.lookup] at hLookup)
    (by
      intro i τ c hLookup hResolved
      cases i with
      | zero => simp [Closure.lookup] at hResolved
      | succ i => simp [Term.lookup] at hLookup), .nil⟩

theorem closureTyping_bind {body : Term} {a : Closure} {ρ : List (Option Closure)}
    {Γ σ τ} (hBody : Term.HasType (σ :: Γ) body τ)
    (hPresent : ∀ {i υ}, Term.lookup Γ i = some υ →
      ∃ entry, Closure.lookup ρ i = some entry)
    (hResolved : ∀ {i υ c}, Term.lookup Γ i = some υ →
      Closure.lookup ρ i = some (some c) → ClosureTyping c υ)
    (hArg : ClosureTyping a σ) :
    ClosureTyping (.mk body (some a :: ρ)) τ := by
  refine .mk hBody ?_ ?_
  · intro i υ hLookup
    cases i with
    | zero => exact ⟨some a, rfl⟩
    | succ i =>
      exact hPresent (by simpa [Term.lookup] using hLookup)
  · intro i υ c hLookup hLookupEnv
    cases i with
    | zero =>
      simp [Term.lookup] at hLookup
      simp [Closure.lookup] at hLookupEnv
      subst υ
      subst c
      exact hArg
    | succ i =>
      exact hResolved (by simpa [Term.lookup] using hLookup)
        (by simpa [Closure.lookup] using hLookupEnv)

theorem typed_machine_step {s t : MachineState} {τ : SimpleTy}
    (hTyped : TypedState s τ) (hStep : MachineStep s t) : TypedState t τ := by
  rcases s with ⟨⟨e, env⟩, k⟩
  rcases hTyped with ⟨σ, hFocus, hKont⟩
  rcases hFocus with ⟨hCode, hPresent, hResolved⟩
  cases hStep with
  | var hLookup =>
    cases hCode with
    | var hTypeLookup =>
      exact ⟨_, hResolved hTypeLookup hLookup, hKont⟩
  | app =>
    cases hCode with
    | app hFun hArg =>
      exact ⟨_, .mk hFun hPresent hResolved,
        .cons (.app (.mk hArg hPresent hResolved)) hKont⟩
  | proj =>
    cases hCode with
    | projLeft hPair =>
      exact ⟨_, .mk hPair hPresent hResolved, .cons .projLeft hKont⟩
    | projRight hPair =>
      exact ⟨_, .mk hPair hPresent hResolved, .cons .projRight hKont⟩
  | op o =>
    cases hCode with
    | op o hLeft hRight =>
      exact ⟨_, .mk hLeft hPresent hResolved,
        .cons (.opLeft o (.mk hRight hPresent hResolved)) hKont⟩
  | ite =>
    cases hCode with
    | ite hCond hThen hElse =>
      exact ⟨_, .mk hCond hPresent hResolved,
        .cons (.ite (.mk hThen hPresent hResolved) (.mk hElse hPresent hResolved)) hKont⟩
  | letE =>
    cases hCode with
    | letE hDef hBody =>
      exact ⟨_, closureTyping_bind hBody hPresent hResolved
        (.mk hDef hPresent hResolved), hKont⟩
  | fix =>
    cases hCode with
    | fix hBody =>
      exact ⟨_, closureTyping_bind hBody hPresent hResolved
        (.mk (Term.HasType.fix hBody) hPresent hResolved), hKont⟩
  | lamApp =>
    cases hCode with
    | lam hBody =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | app hArg =>
          exact ⟨_, closureTyping_bind hBody hPresent hResolved hArg, hRest⟩
  | projLeft =>
    cases hCode with
    | pair hLeft hRight =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | projLeft => exact ⟨_, .mk hLeft hPresent hResolved, hRest⟩
  | projRight =>
    cases hCode with
    | pair hLeft hRight =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | projRight => exact ⟨_, .mk hRight hPresent hResolved, hRest⟩
  | opLeft o =>
    cases hCode with
    | int =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | opLeft o hArg => exact ⟨_, hArg, .cons (.opRight o) hRest⟩
  | opRight o =>
    cases hCode with
    | int =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | opRight o => exact ⟨_, .mk .int hPresent hResolved, hRest⟩
  | ifTrue hn =>
    cases hCode with
    | int =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | ite hThen hElse => exact ⟨_, hThen, hRest⟩
  | ifFalse =>
    cases hCode with
    | int =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | ite hThen hElse => exact ⟨_, hElse, hRest⟩
  | omega => exact ⟨_, .mk hCode hPresent hResolved, hKont⟩

theorem typed_machine_steps {s t : MachineState} {τ : SimpleTy}
    (hTyped : TypedState s τ) (hSteps : MachineSteps s t) : TypedState t τ := by
  induction hSteps with
  | refl => exact hTyped
  | tail hSteps hStep ih => exact typed_machine_step ih hStep

/-- A well-typed machine state whose final answer type is `Int` cannot get
stuck.  Its only genuine terminals are an unresolved demand, `err`, and an
integer with an empty continuation. -/
theorem typed_terminal_forms {s : MachineState}
    (hTyped : TypedState s .int) (hTerminal : MachineState.Terminal s) :
    MachineState.Demands s ∨ MachineState.IsError s ∨
      ∃ n, MachineState.ReturnsInt s n := by
  rcases s with ⟨⟨e, env⟩, k⟩
  rcases hTyped with ⟨σ, hFocus, hKont⟩
  rcases hFocus with ⟨hCode, hPresent, hResolved⟩
  cases e with
  | var i =>
    cases hCode with
    | var hLookup =>
      rcases hPresent hLookup with ⟨entry, hEntry⟩
      cases entry with
      | none => exact .inl hEntry
      | some c => exact False.elim (hTerminal _ (.var hEntry))
  | int n =>
    cases hCode
    cases hKont with
    | nil => exact .inr (.inr ⟨n, env, rfl⟩)
    | cons hFrame hRest =>
      cases hFrame with
      | opLeft o hArg => exact False.elim (hTerminal _ (.opLeft o))
      | opRight o => exact False.elim (hTerminal _ (.opRight o))
      | ite hThen hElse =>
        by_cases hn : n = 0
        · subst n
          exact False.elim (hTerminal _ .ifFalse)
        · exact False.elim (hTerminal _ (.ifTrue hn))
  | lam body =>
    cases hCode with
    | lam hBody =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | app hArg => exact False.elim (hTerminal _ .lamApp)
  | app e₁ e₂ => exact False.elim (hTerminal _ .app)
  | pair e₁ e₂ =>
    cases hCode with
    | pair hLeft hRight =>
      cases hKont with
      | cons hFrame hRest =>
        cases hFrame with
        | projLeft => exact False.elim (hTerminal _ .projLeft)
        | projRight => exact False.elim (hTerminal _ .projRight)
  | proj b e => exact False.elim (hTerminal _ .proj)
  | op o e₁ e₂ => exact False.elim (hTerminal _ (.op o))
  | ite e₀ e₁ e₂ => exact False.elim (hTerminal _ .ite)
  | letE e₁ e₂ => exact False.elim (hTerminal _ .letE)
  | fix body => exact False.elim (hTerminal _ .fix)
  | omega => exact False.elim (hTerminal _ .omega)
  | err => exact .inr (.inl trivial)

end Strictness
