import Strictness.Language.SimpleInstantiation
import Strictness.Operational.BigStep

/-!
Call-by-name source reduction.

Defines evaluation contexts, primitive contractions, finite reduction and
infinite executions. An exposed `E[err]` is a terminal error observation.
No closure-machine or semantic-soundness proof is needed by this module.
-/

namespace Strictness

open Term

/-- Call-by-name evaluation contexts for the source language.

There is deliberately no frame below a lambda, a pair component, an
application argument, or a let body.  `let` contracts at the outermost
redex, thereby retaining call-by-name sharing-free substitution semantics. -/
inductive EvalCtx where
  | hole : EvalCtx
  | appFun : EvalCtx → Term → EvalCtx
  | proj : Bool → EvalCtx → EvalCtx
  | opLeft : PrimOp → EvalCtx → Term → EvalCtx
  | opRight : PrimOp → Int → EvalCtx → EvalCtx
  | ite : EvalCtx → Term → Term → EvalCtx
  deriving DecidableEq, Repr

namespace EvalCtx

def plug : EvalCtx → Term → Term
  | .hole, e => e
  | .appFun E a, e => .app (plug E e) a
  | .proj b E, e => .proj b (plug E e)
  | .opLeft o E e₂, e => .op o (plug E e) e₂
  | .opRight o n E, e => .op o (.int n) (plug E e)
  | .ite E e₁ e₂, e => .ite (plug E e) e₁ e₂

/-- Apply a closing substitution to the fixed terms carried by a context. -/
def map (ρ : Substitution) : EvalCtx → EvalCtx
  | .hole => .hole
  | .appFun E a => .appFun (map ρ E) (Substitution.apply ρ a)
  | .proj b E => .proj b (map ρ E)
  | .opLeft o E e₂ => .opLeft o (map ρ E) (Substitution.apply ρ e₂)
  | .opRight o n E => .opRight o n (map ρ E)
  | .ite E e₁ e₂ => .ite (map ρ E) (Substitution.apply ρ e₁)
      (Substitution.apply ρ e₂)

@[simp] theorem plug_hole (e : Term) : plug .hole e = e := rfl

/-- A demanded occurrence of the single open variable. -/
def Demanded (e : Term) : Prop := ∃ E, e = plug E (.var 0)

end EvalCtx

/-- Primitive CBN contractions.  Contextual closure is defined below. -/
inductive RootStep : Term → Term → Prop where
  | beta {body a : Term} :
      RootStep (.app (.lam body) a) (Term.instantiate body a)
  | projLeft {e₁ e₂ : Term} :
      RootStep (.proj true (.pair e₁ e₂)) e₁
  | projRight {e₁ e₂ : Term} :
      RootStep (.proj false (.pair e₁ e₂)) e₂
  | op (o : PrimOp) {n₁ n₂ : Int} :
      RootStep (.op o (.int n₁) (.int n₂)) (.int (o.eval n₁ n₂))
  | ifTrue {n : Int} {e₁ e₂ : Term} :
      n ≠ 0 → RootStep (.ite (.int n) e₁ e₂) e₁
  | ifFalse {e₁ e₂ : Term} :
      RootStep (.ite (.int 0) e₁ e₂) e₂
  | letE {e₁ e₂ : Term} :
      RootStep (.letE e₁ e₂) (Term.instantiate e₂ e₁)
  | fix {body : Term} :
      RootStep (.fix body) (Term.instantiate body (.fix body))
  /-- The semantic divergent marker has a self transition. -/
  | omega : RootStep .omega .omega

/-- One open-term CBN reduction step. -/
def Step (e e' : Term) : Prop :=
  ∃ E r r', RootStep r r' ∧ e = EvalCtx.plug E r ∧ e' = EvalCtx.plug E r'

/-- Reflexive transitive closure of open reduction. -/
inductive Steps (e : Term) : Term → Prop where
  | refl : Steps e e
  | tail {e' e'' : Term} : Steps e e' → Step e' e'' → Steps e e''

namespace EvalCtx

@[simp] theorem plug_err_evalErr (E : EvalCtx) : EvalErr (plug E .err) := by
  induction E with
  | hole => exact EvalErr.err
  | appFun E a ih => exact EvalErr.appFun ih
  | proj b E ih => exact EvalErr.projScrutinee ih
  | opLeft o E e₂ ih => exact EvalErr.opLeft o ih
  | opRight o n E ih => exact EvalErr.opRight o Eval.int ih
  | ite E e₁ e₂ ih => exact EvalErr.ifCond ih

/-- An error observation is preserved by every CBN evaluation
context. -/
theorem plug_evalErr (E : EvalCtx) {e : Term} :
    EvalErr e → EvalErr (plug E e) := by
  intro h
  induction E generalizing e with
  | hole => exact h
  | appFun E a ih => exact EvalErr.appFun (ih h)
  | proj b E ih => exact EvalErr.projScrutinee (ih h)
  | opLeft o E e₂ ih => exact EvalErr.opLeft o (ih h)
  | opRight o n E ih => exact EvalErr.opRight o Eval.int (ih h)
  | ite E e₁ e₂ ih => exact EvalErr.ifCond (ih h)

@[simp] theorem apply_plug (ρ : Substitution) (E : EvalCtx) (e : Term) :
    Substitution.apply ρ (plug E e) = plug (map ρ E) (Substitution.apply ρ e) := by
  induction E generalizing e with
  | hole => rfl
  | appFun E a ih =>
      simpa [plug, map, Substitution.apply, Substitution.applyAt] using
        congrArg (fun z => Term.app z (Substitution.apply ρ a)) (ih e)
  | proj b E ih =>
      simpa [plug, map, Substitution.apply, Substitution.applyAt] using
        congrArg (fun z => Term.proj b z) (ih e)
  | opLeft o E e₂ ih =>
      simpa [plug, map, Substitution.apply, Substitution.applyAt] using
        congrArg (fun z => Term.op o z (Substitution.apply ρ e₂)) (ih e)
  | opRight o n E ih =>
      simpa [plug, map, Substitution.apply, Substitution.applyAt] using
        congrArg (fun z => Term.op o (.int n) z) (ih e)
  | ite E e₁ e₂ ih =>
      simpa [plug, map, Substitution.apply, Substitution.applyAt] using
        congrArg (fun z => Term.ite z (Substitution.apply ρ e₁)
          (Substitution.apply ρ e₂)) (ih e)

/-- Substituting `err` into a demanded occurrence reaches the error
observation immediately. -/
theorem demanded_err {e : Term} (h : Demanded e) :
    EvalErr (Substitution.apply (singleSubst .err) e) := by
  rcases h with ⟨E, rfl⟩
  rw [apply_plug]
  change EvalErr (plug (map (singleSubst .err) E) .err)
  exact plug_err_evalErr _

end EvalCtx

/-- Closing a source term with a closed semantic substitution does not leave
free variables.  This elementary fact is kept local because the operational
bridge only ever uses closed semantic test terms (`omega` and `err`). -/
theorem apply_closed_of_closed_images
    (ρ : Substitution) (hρ : ∀ i, Term.Closed (ρ i)) (e : Term) :
    Term.Closed (Substitution.apply ρ e) := by
  have closedAt_mono :
      ∀ {d d' e}, Term.ClosedAt d e → d ≤ d' → Term.ClosedAt d' e := by
    intro d d' e h hle
    induction e generalizing d d' with
    | var i => exact Nat.lt_of_lt_of_le h hle
    | int n => trivial
    | lam body ih =>
        exact ih h (Nat.succ_le_succ hle)
    | fix body ih =>
        exact ih h (Nat.succ_le_succ hle)
    | app e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ h.1 hle, ih₂ h.2 hle⟩
    | pair e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ h.1 hle, ih₂ h.2 hle⟩
    | proj b e ih => exact ih h hle
    | op o e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ h.1 hle, ih₂ h.2 hle⟩
    | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
        exact ⟨ih₀ h.1 hle, ih₁ h.2.1 hle, ih₂ h.2.2 hle⟩
    | letE e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ h.1 hle, ih₂ h.2 (Nat.succ_le_succ hle)⟩
    | omega => trivial
    | err => trivial
  have go : ∀ d e, Term.ClosedAt d (Substitution.applyAt ρ d e) := by
    intro d e
    induction e generalizing d with
    | var i =>
        by_cases h : i < d
        · simp [Substitution.applyAt, h]
        · have himage := hρ (i - d)
          have hshift :
              Term.ClosedAt d (Term.shift d 0 (ρ (i - d))) := by
            rw [Term.shift_eq_of_closed himage]
            exact closedAt_mono himage (Nat.zero_le _)
          simp [Substitution.applyAt, h, hshift]
    | int n => trivial
    | lam body ih =>
        simpa [Substitution.applyAt, Term.ClosedAt] using ih (d + 1)
    | fix body ih =>
        simpa [Substitution.applyAt, Term.ClosedAt] using ih (d + 1)
    | app e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ d, ih₂ d⟩
    | pair e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ d, ih₂ d⟩
    | proj b e ih => exact ih d
    | op o e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ d, ih₂ d⟩
    | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
        exact ⟨ih₀ d, ih₁ d, ih₂ d⟩
    | letE e₁ e₂ ih₁ ih₂ =>
        exact ⟨ih₁ d, ih₂ (d + 1)⟩
    | omega => trivial
    | err => trivial
  simpa [Substitution.apply, Term.Closed] using go 0 e


/-- An operational infinite execution represented as an infinite sequence of
CBN source transitions. -/
def InfiniteSteps (e : Term) : Prop :=
  ∃ run : Nat → Term, run 0 = e ∧ ∀ n, Step (run n) (run (n + 1))


end Strictness
