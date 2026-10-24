import Strictness.Semantics.FixApproximation

namespace Strictness
namespace Term

/-- Structural approximation: omega may be replaced by any term, while
all other constructors retain their shape. This relation does not itself
identify a fix term with its unfolding. -/
inductive Approx : Term → Term → Prop where
  | bottom {e : Term} : Approx .omega e
  | var (i : Nat) : Approx (.var i) (.var i)
  | int (n : Int) : Approx (.int n) (.int n)
  | err : Approx .err .err
  | lam {b b' : Term} :
      Approx b b' → Approx (.lam b) (.lam b')
  | fix {b b' : Term} :
      Approx b b' → Approx (.fix b) (.fix b')
  | app {f f' a a' : Term} :
      Approx f f' → Approx a a' → Approx (.app f a) (.app f' a')
  | pair {a a' b b' : Term} :
      Approx a a' → Approx b b' → Approx (.pair a b) (.pair a' b')
  | proj {b : Bool} {e e' : Term} :
      Approx e e' → Approx (.proj b e) (.proj b e')
  | op (o : PrimOp) {a a' b b' : Term} :
      Approx a a' → Approx b b' → Approx (.op o a b) (.op o a' b')
  | ite {c c' t t' f f' : Term} :
      Approx c c' → Approx t t' → Approx f f' →
      Approx (.ite c t f) (.ite c' t' f')
  | letE {a a' b b' : Term} :
      Approx a a' → Approx b b' → Approx (.letE a b) (.letE a' b')

theorem Approx.refl (e : Term) : Approx e e := by
  induction e with
  | var i => exact Approx.var i
  | int n => exact Approx.int n
  | lam body ih => exact Approx.lam ih
  | fix body ih => exact Approx.fix ih
  | app f a ihf iha => exact Approx.app ihf iha
  | pair a b iha ihb => exact Approx.pair iha ihb
  | proj b e ih => exact Approx.proj ih
  | op o a b iha ihb => exact Approx.op o iha ihb
  | ite c t f ihc iht ihf => exact Approx.ite ihc iht ihf
  | letE a b iha ihb => exact Approx.letE iha ihb
  | omega => exact Approx.bottom
  | err => exact Approx.err

/-- De Bruijn shifting preserves structural approximation. -/
theorem Approx.shift {e e' : Term} (h : Approx e e')
    (amount cutoff : Nat) :
    Approx (Term.shift amount cutoff e) (Term.shift amount cutoff e') := by
  induction h generalizing cutoff with
  | bottom => exact Approx.bottom
  | var i =>
      by_cases hi : cutoff ≤ i
      · simpa only [Term.shift, if_pos hi] using (Approx.var (i + amount))
      · simpa only [Term.shift, if_neg hi] using (Approx.var i)
  | int n => exact Approx.int n
  | err => exact Approx.err
  | lam h ih => exact Approx.lam (ih (cutoff + 1))
  | fix h ih => exact Approx.fix (ih (cutoff + 1))
  | app hf ha ihf iha => exact Approx.app (ihf cutoff) (iha cutoff)
  | pair ha hb iha ihb => exact Approx.pair (iha cutoff) (ihb cutoff)
  | proj h ih => exact Approx.proj (ih cutoff)
  | op o ha hb iha ihb => exact Approx.op o (iha cutoff) (ihb cutoff)
  | ite hc ht hf ihc iht ihf =>
      exact Approx.ite (ihc cutoff) (iht cutoff) (ihf cutoff)
  | letE ha hb iha ihb =>
      exact Approx.letE (iha cutoff) (ihb (cutoff + 1))

/-- Substitution preserves approximation in both the body and the argument. -/
theorem Approx.subst {e e' s s' : Term}
    (h : Approx e e') (hArg : Approx s s') (j : Nat) :
    Approx (Term.subst j s e) (Term.subst j s' e') := by
  induction h generalizing j s s' with
  | bottom => exact Approx.bottom
  | var i =>
      by_cases hEq : i = j
      · simpa only [Term.subst, if_pos hEq] using hArg
      · by_cases hLt : j < i
        · simpa only [Term.subst, if_neg hEq, if_pos hLt] using
            (Approx.var (i - 1))
        · simpa only [Term.subst, if_neg hEq, if_neg hLt] using
            (Approx.var i)
  | int n => exact Approx.int n
  | err => exact Approx.err
  | lam h ih =>
      exact Approx.lam
        (ih (j := j + 1) (s := Term.shift 1 0 s) (s' := Term.shift 1 0 s')
          (Approx.shift hArg 1 0))
  | fix h ih =>
      exact Approx.fix
        (ih (j := j + 1) (s := Term.shift 1 0 s) (s' := Term.shift 1 0 s')
          (Approx.shift hArg 1 0))
  | app hf ha ihf iha =>
      exact Approx.app (ihf (j := j) hArg) (iha (j := j) hArg)
  | pair ha hb iha ihb =>
      exact Approx.pair (iha (j := j) hArg) (ihb (j := j) hArg)
  | proj h ih =>
      exact Approx.proj (ih (j := j) hArg)
  | op o ha hb iha ihb =>
      exact Approx.op o (iha (j := j) hArg) (ihb (j := j) hArg)
  | ite hc ht hf ihc iht ihf =>
      exact Approx.ite
        (ihc (j := j) hArg) (iht (j := j) hArg) (ihf (j := j) hArg)
  | letE ha hb iha ihb =>
      exact Approx.letE (iha (j := j) hArg)
        (ihb (j := j + 1) (s := Term.shift 1 0 s) (s' := Term.shift 1 0 s')
          (Approx.shift hArg 1 0))

/-- Instantiation is monotone in the binder body and its substituted argument. -/
theorem Approx.instantiate {body body' arg arg' : Term}
    (hBody : Approx body body') (hArg : Approx arg arg') :
    Approx (Term.instantiate body arg) (Term.instantiate body' arg') := by
  exact Approx.subst hBody hArg 0

end Term
end Strictness
