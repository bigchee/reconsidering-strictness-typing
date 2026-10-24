import Strictness.Semantics.FixSemantics

/-!
Representation of the auxiliary divergence marker by source self recursion.

`Term.OmegaEq` permits selected occurrences of `.omega` and `.fix (.var 0)`
to be interchanged. `Term.expandOmega` expands every marker and commutes
with variable operations while preserving and reflecting scope and simple
typing. `OmegaFree` certifies absence of auxiliary markers; `err` remains
available as an observation probe.
-/

namespace Strictness
namespace Term

/-- Structural replacement of the semantic divergence marker by the canonical
source loop, in either direction and at any selected occurrences. -/
inductive OmegaEq : Term → Term → Prop where
  | omega : OmegaEq .omega .omega
  | expand : OmegaEq .omega (.fix (.var 0))
  | contract : OmegaEq (.fix (.var 0)) .omega
  | var (i : Nat) : OmegaEq (.var i) (.var i)
  | int (n : Int) : OmegaEq (.int n) (.int n)
  | err : OmegaEq .err .err
  | lam {b b' : Term} :
      OmegaEq b b' → OmegaEq (.lam b) (.lam b')
  | fix {b b' : Term} :
      OmegaEq b b' → OmegaEq (.fix b) (.fix b')
  | app {f f' a a' : Term} :
      OmegaEq f f' → OmegaEq a a' → OmegaEq (.app f a) (.app f' a')
  | pair {a a' b b' : Term} :
      OmegaEq a a' → OmegaEq b b' → OmegaEq (.pair a b) (.pair a' b')
  | proj {b : Bool} {e e' : Term} :
      OmegaEq e e' → OmegaEq (.proj b e) (.proj b e')
  | op (o : PrimOp) {a a' b b' : Term} :
      OmegaEq a a' → OmegaEq b b' → OmegaEq (.op o a b) (.op o a' b')
  | ite {c c' t t' f f' : Term} :
      OmegaEq c c' → OmegaEq t t' → OmegaEq f f' →
      OmegaEq (.ite c t f) (.ite c' t' f')
  | letE {a a' b b' : Term} :
      OmegaEq a a' → OmegaEq b b' → OmegaEq (.letE a b) (.letE a' b')

theorem OmegaEq.refl (e : Term) : OmegaEq e e := by
  induction e with
  | var i => exact OmegaEq.var i
  | int n => exact OmegaEq.int n
  | lam body ih => exact OmegaEq.lam ih
  | fix body ih => exact OmegaEq.fix ih
  | app f a ihf iha => exact OmegaEq.app ihf iha
  | pair a b iha ihb => exact OmegaEq.pair iha ihb
  | proj b e ih => exact OmegaEq.proj ih
  | op o a b iha ihb => exact OmegaEq.op o iha ihb
  | ite c t f ihc iht ihf => exact OmegaEq.ite ihc iht ihf
  | letE a b iha ihb => exact OmegaEq.letE iha ihb
  | omega => exact OmegaEq.omega
  | err => exact OmegaEq.err

/-- De Bruijn shifting preserves structural replacement. -/
theorem OmegaEq.shift {e e' : Term} (h : OmegaEq e e')
    (amount cutoff : Nat) :
    OmegaEq (Term.shift amount cutoff e) (Term.shift amount cutoff e') := by
  induction h generalizing cutoff with
  | omega => exact OmegaEq.omega
  | expand => simpa [Term.shift, Term.subst] using OmegaEq.expand
  | contract => simpa [Term.shift, Term.subst] using OmegaEq.contract
  | var i =>
      by_cases hi : cutoff ≤ i
      · simpa only [Term.shift, if_pos hi] using (OmegaEq.var (i + amount))
      · simpa only [Term.shift, if_neg hi] using (OmegaEq.var i)
  | int n => exact OmegaEq.int n
  | err => exact OmegaEq.err
  | lam h ih => exact OmegaEq.lam (ih (cutoff + 1))
  | fix h ih => exact OmegaEq.fix (ih (cutoff + 1))
  | app hf ha ihf iha => exact OmegaEq.app (ihf cutoff) (iha cutoff)
  | pair ha hb iha ihb => exact OmegaEq.pair (iha cutoff) (ihb cutoff)
  | proj h ih => exact OmegaEq.proj (ih cutoff)
  | op o ha hb iha ihb => exact OmegaEq.op o (iha cutoff) (ihb cutoff)
  | ite hc ht hf ihc iht ihf =>
      exact OmegaEq.ite (ihc cutoff) (iht cutoff) (ihf cutoff)
  | letE ha hb iha ihb =>
      exact OmegaEq.letE (iha cutoff) (ihb (cutoff + 1))

/-- Substitution preserves replacement in both the body and the argument. -/
theorem OmegaEq.subst {e e' s s' : Term}
    (h : OmegaEq e e') (hArg : OmegaEq s s') (j : Nat) :
    OmegaEq (Term.subst j s e) (Term.subst j s' e') := by
  induction h generalizing j s s' with
  | omega => exact OmegaEq.omega
  | expand => simpa [Term.subst] using OmegaEq.expand
  | contract => simpa [Term.subst] using OmegaEq.contract
  | var i =>
      by_cases hEq : i = j
      · simpa only [Term.subst, if_pos hEq] using hArg
      · by_cases hLt : j < i
        · simpa only [Term.subst, if_neg hEq, if_pos hLt] using
            (OmegaEq.var (i - 1))
        · simpa only [Term.subst, if_neg hEq, if_neg hLt] using
            (OmegaEq.var i)
  | int n => exact OmegaEq.int n
  | err => exact OmegaEq.err
  | lam h ih =>
      exact OmegaEq.lam
        (ih (j := j + 1) (s := Term.shift 1 0 s) (s' := Term.shift 1 0 s')
          (OmegaEq.shift hArg 1 0))
  | fix h ih =>
      exact OmegaEq.fix
        (ih (j := j + 1) (s := Term.shift 1 0 s) (s' := Term.shift 1 0 s')
          (OmegaEq.shift hArg 1 0))
  | app hf ha ihf iha =>
      exact OmegaEq.app (ihf (j := j) hArg) (iha (j := j) hArg)
  | pair ha hb iha ihb =>
      exact OmegaEq.pair (iha (j := j) hArg) (ihb (j := j) hArg)
  | proj h ih =>
      exact OmegaEq.proj (ih (j := j) hArg)
  | op o ha hb iha ihb =>
      exact OmegaEq.op o (iha (j := j) hArg) (ihb (j := j) hArg)
  | ite hc ht hf ihc iht ihf =>
      exact OmegaEq.ite
        (ihc (j := j) hArg) (iht (j := j) hArg) (ihf (j := j) hArg)
  | letE ha hb iha ihb =>
      exact OmegaEq.letE (iha (j := j) hArg)
        (ihb (j := j + 1) (s := Term.shift 1 0 s) (s' := Term.shift 1 0 s')
          (OmegaEq.shift hArg 1 0))

/-- Instantiation preserves replacement in both the binder body and its argument. -/
theorem OmegaEq.instantiate {body body' arg arg' : Term}
    (hBody : OmegaEq body body') (hArg : OmegaEq arg arg') :
    OmegaEq (Term.instantiate body arg) (Term.instantiate body' arg') := by
  exact OmegaEq.subst hBody hArg 0

theorem OmegaEq.symm {e e' : Term} (h : OmegaEq e e') : OmegaEq e' e := by
  induction h with
  | omega => exact .omega
  | expand => exact .contract
  | contract => exact .expand
  | var i => exact .var i
  | int n => exact .int n
  | err => exact .err
  | lam _ ih => exact .lam ih
  | fix _ ih => exact .fix ih
  | app _ _ ihf iha => exact .app ihf iha
  | pair _ _ iha ihb => exact .pair iha ihb
  | proj _ ih => exact .proj ih
  | op o _ _ iha ihb => exact .op o iha ihb
  | ite _ _ _ ihc iht ihf => exact .ite ihc iht ihf
  | letE _ _ iha ihb => exact .letE iha ihb

theorem OmegaEq.hasType {e e' : Term} (h : OmegaEq e e')
    {Γ : Ctx} {A : SimpleTy} (ht : HasType Γ e A) : HasType Γ e' A := by
  induction h generalizing Γ A with
  | omega => exact .omega
  | expand => exact .fix (.var rfl)
  | contract => exact .omega
  | var i => exact ht
  | int n => exact ht
  | err => exact .err
  | lam h ih => cases ht with | lam hb => exact .lam (ih hb)
  | fix h ih => cases ht with | fix hb => exact .fix (ih hb)
  | app hf ha ihf iha => cases ht with | app hf ha => exact .app (ihf hf) (iha ha)
  | pair ha hb iha ihb => cases ht with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | proj h ih => cases ht with
    | projLeft hp => exact .projLeft (ih hp)
    | projRight hp => exact .projRight (ih hp)
  | op o ha hb iha ihb => cases ht with | op _ ha hb => exact .op o (iha ha) (ihb hb)
  | ite hc ht hf ihc iht ihf => cases ht with
    | ite hc ht hf => exact .ite (ihc hc) (iht ht) (ihf hf)
  | letE ha hb iha ihb => cases ht with | letE ha hb => exact .letE (iha ha) (ihb hb)

theorem OmegaEq.closedAt {e e' : Term} (h : OmegaEq e e') (d : Nat) :
    ClosedAt d e ↔ ClosedAt d e' := by
  induction h generalizing d <;> simp_all [ClosedAt]

/-- Expand all semantic divergence markers into source-language self recursion. -/
def expandOmega : Term → Term
  | .omega => .fix (.var 0)
  | .var i => .var i
  | .int n => .int n
  | .err => .err
  | .lam b => .lam (expandOmega b)
  | .fix b => .fix (expandOmega b)
  | .app f a => .app (expandOmega f) (expandOmega a)
  | .pair a b => .pair (expandOmega a) (expandOmega b)
  | .proj b e => .proj b (expandOmega e)
  | .op o a b => .op o (expandOmega a) (expandOmega b)
  | .ite c t f => .ite (expandOmega c) (expandOmega t) (expandOmega f)
  | .letE a b => .letE (expandOmega a) (expandOmega b)

theorem omegaEq_expandOmega (e : Term) : OmegaEq e (expandOmega e) := by
  induction e with
  | omega => exact .expand
  | var i => exact .var i
  | int n => exact .int n
  | err => exact .err
  | lam _ ih => exact .lam ih
  | fix _ ih => exact .fix ih
  | app _ _ ihf iha => exact .app ihf iha
  | pair _ _ iha ihb => exact .pair iha ihb
  | proj _ _ ih => exact .proj ih
  | op o _ _ iha ihb => exact .op o iha ihb
  | ite _ _ _ ihc iht ihf => exact .ite ihc iht ihf
  | letE _ _ iha ihb => exact .letE iha ihb

theorem expandOmega_shift (e : Term) (a c : Nat) :
    expandOmega (shift a c e) = shift a c (expandOmega e) := by
  induction e generalizing c <;> simp_all [expandOmega, shift]
  case var i => split <;> rfl

theorem expandOmega_subst (e s : Term) (j : Nat) :
    expandOmega (subst j s e) = subst j (expandOmega s) (expandOmega e) := by
  induction e generalizing j s <;> simp_all [expandOmega, subst, expandOmega_shift]
  case var i => split <;> (try split) <;> rfl

theorem expandOmega_instantiate (b a : Term) :
    expandOmega (instantiate b a) = instantiate (expandOmega b) (expandOmega a) :=
  expandOmega_subst b a 0

/-- Finite source approximations start at the explicit source loop. -/
def sourceFixApprox (body : Term) : Nat → Term
  | 0 => .fix (.var 0)
  | n + 1 => instantiate body (sourceFixApprox body n)

/-- No occurrence of the auxiliary semantic constructor remains. -/
def OmegaFree : Term → Prop
  | .omega => False
  | .var _ | .int _ | .err => True
  | .lam b | .fix b | .proj _ b => OmegaFree b
  | .app a b | .pair a b | .op _ a b | .letE a b => OmegaFree a ∧ OmegaFree b
  | .ite c t f => OmegaFree c ∧ OmegaFree t ∧ OmegaFree f

theorem expandOmega_omegaFree (e : Term) : OmegaFree e.expandOmega := by
  induction e <;> simp_all [expandOmega, OmegaFree]

theorem expandOmega_eq_of_omegaFree {e : Term} (h : OmegaFree e) : e.expandOmega = e := by
  induction e <;> simp_all [OmegaFree, expandOmega]

theorem expandOmega_idempotent (e : Term) : e.expandOmega.expandOmega = e.expandOmega :=
  expandOmega_eq_of_omegaFree (expandOmega_omegaFree e)

theorem expandOmega_hasType_iff {e : Term} {Γ : Ctx} {A : SimpleTy} :
    HasType Γ e.expandOmega A ↔ HasType Γ e A :=
  ⟨fun h => (omegaEq_expandOmega e).symm.hasType h,
   fun h => (omegaEq_expandOmega e).hasType h⟩

theorem expandOmega_closed_iff (e : Term) : Closed e.expandOmega ↔ Closed e :=
  ((omegaEq_expandOmega e).closedAt 0).symm

end Term

namespace Substitution

/-- Expansion commutes with simultaneous substitution at any binder depth. -/
theorem expandOmega_applyAt (ρ : Substitution) (d : Nat) (e : Term) :
    (applyAt ρ d e).expandOmega = applyAt (fun i => (ρ i).expandOmega) d e.expandOmega := by
  induction e generalizing d <;>
    simp_all [applyAt, Term.expandOmega]
  case var i =>
    split
    · rfl
    · exact Term.expandOmega_shift _ _ _

theorem expandOmega_apply (ρ : Substitution) (e : Term) :
    (apply ρ e).expandOmega = apply (fun i => (ρ i).expandOmega) e.expandOmega :=
  expandOmega_applyAt ρ 0 e

end Substitution
end Strictness
