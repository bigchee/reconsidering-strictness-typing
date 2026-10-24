import Strictness.Language.Type

namespace Strictness

/-- Primitive arithmetic operations. Each interpretation is total on integers.
The soundness proofs are uniform in the operator and use no arithmetic laws. -/
inductive PrimOp where
  | add | sub | mul
  deriving DecidableEq, Repr

namespace PrimOp

/-- Integer interpretation; both operands are evaluated before this is used. -/
def eval : PrimOp → Int → Int → Int
  | .add, n₁, n₂ => n₁ + n₂
  | .sub, n₁, n₂ => n₁ - n₂
  | .mul, n₁, n₂ => n₁ * n₂

end PrimOp

/-- Terms used by the operational semantics.

We use De Bruijn indices, as in Smetsers--van Eekelen.  `fix body`
binds index zero in `body`, just like `lam body`.  `omega` and `err`
are semantic additions: they are not source-language constructs, but are
available when reasoning about divergence and error propagation.
-/
inductive Term where
  | var  : Nat → Term
  | int  : Int → Term
  | lam  : Term → Term
  | fix  : Term → Term
  | app  : Term → Term → Term
  | pair : Term → Term → Term
  | proj : Bool → Term → Term
  | op  : PrimOp → Term → Term → Term
  | ite  : Term → Term → Term → Term
  | letE : Term → Term → Term
  | omega : Term
  | err : Term
  deriving DecidableEq, Repr

namespace Term

/-- `closedAt d e` means that `e` has no free De Bruijn index at depth `d`. -/
def ClosedAt : Nat → Term → Prop
  | d, .var i => i < d
  | _, .int _ => True
  | d, .lam body => ClosedAt (d + 1) body
  | d, .fix body => ClosedAt (d + 1) body
  | d, .app e₁ e₂ => ClosedAt d e₁ ∧ ClosedAt d e₂
  | d, .pair e₁ e₂ => ClosedAt d e₁ ∧ ClosedAt d e₂
  | d, .proj _ e => ClosedAt d e
  | d, .op _ e₁ e₂ => ClosedAt d e₁ ∧ ClosedAt d e₂
  | d, .ite e₀ e₁ e₂ => ClosedAt d e₀ ∧ ClosedAt d e₁ ∧ ClosedAt d e₂
  | d, .letE e₁ e₂ => ClosedAt d e₁ ∧ ClosedAt (d + 1) e₂
  | _, .omega => True
  | _, .err => True

def Closed (e : Term) : Prop := ClosedAt 0 e

@[simp] theorem closedAt_var {d i : Nat} : ClosedAt d (.var i) ↔ i < d := Iff.rfl

@[simp] theorem closedAt_lam {d : Nat} {e : Term} :
    ClosedAt d (.lam e) ↔ ClosedAt (d + 1) e := Iff.rfl

@[simp] theorem closed_lam {e : Term} : Closed (.lam e) ↔ ClosedAt 1 e := by
  rfl

@[simp] theorem closedAt_fix {d : Nat} {e : Term} :
    ClosedAt d (.fix e) ↔ ClosedAt (d + 1) e := Iff.rfl

@[simp] theorem closed_fix {e : Term} :
    Closed (.fix e) ↔ ClosedAt 1 e := Iff.rfl

/-- A standard De Bruijn shift. -/
def shift (amount cutoff : Nat) : Term → Term
  | .var i =>
      if cutoff ≤ i then .var (i + amount) else .var i
  | .int n => .int n
  | .lam body => .lam (shift amount (cutoff + 1) body)
  | .fix body => .fix (shift amount (cutoff + 1) body)
  | .app e₁ e₂ => .app (shift amount cutoff e₁) (shift amount cutoff e₂)
  | .pair e₁ e₂ => .pair (shift amount cutoff e₁) (shift amount cutoff e₂)
  | .proj b e => .proj b (shift amount cutoff e)
  | .op o e₁ e₂ => .op o (shift amount cutoff e₁) (shift amount cutoff e₂)
  | .ite e₀ e₁ e₂ =>
      .ite (shift amount cutoff e₀) (shift amount cutoff e₁) (shift amount cutoff e₂)
  | .letE e₁ e₂ =>
      .letE (shift amount cutoff e₁) (shift amount (cutoff + 1) e₂)
  | .omega => .omega
  | .err => .err

@[simp] theorem shift_zero (cutoff : Nat) (e : Term) :
    shift 0 cutoff e = e := by
  induction e generalizing cutoff <;> simp [shift, *]

/-- De Bruijn substitution `[j := s]e`.

The argument is shifted when descending under a binder, so this is the
usual capture-avoiding substitution operation.
-/
def subst (j : Nat) (s : Term) : Term → Term
  | .var i =>
      if i = j then s
      else if j < i then .var (i - 1)
      else .var i
  | .int n => .int n
  | .lam body => .lam (subst (j + 1) (shift 1 0 s) body)
  | .fix body => .fix (subst (j + 1) (shift 1 0 s) body)
  | .app e₁ e₂ => .app (subst j s e₁) (subst j s e₂)
  | .pair e₁ e₂ => .pair (subst j s e₁) (subst j s e₂)
  | .proj b e => .proj b (subst j s e)
  | .op o e₁ e₂ => .op o (subst j s e₁) (subst j s e₂)
  | .ite e₀ e₁ e₂ =>
      .ite (subst j s e₀) (subst j s e₁) (subst j s e₂)
  | .letE e₁ e₂ =>
      .letE (subst j s e₁) (subst (j + 1) (shift 1 0 s) e₂)
  | .omega => .omega
  | .err => .err

/-- Substitution for the nearest binder, used by beta reduction and fix unfolding. -/
def instantiate (body arg : Term) : Term := subst 0 arg body

end Term


namespace Term

/-- Shifting at a De Bruijn cutoff preserves the `ClosedAt` predicate. -/
theorem closedAt_shift_iff {d amount : Nat} {e : Term} :
    ClosedAt d (shift amount d e) ↔ ClosedAt d e := by
  induction e generalizing d with
  | var i =>
      by_cases hdi : d ≤ i
      · simp [shift, hdi, Nat.not_lt_of_ge hdi]; exact Nat.le_trans hdi (Nat.le_add_right i amount)
      · simp [shift, hdi]
  | int n => simp [ClosedAt, shift]
  | lam body ih =>
      simp [ClosedAt, shift, ih]
  | fix body ih =>
      simp [ClosedAt, shift, ih]
  | app e₁ e₂ ih₁ ih₂ =>
      simp [ClosedAt, shift, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ =>
      simp [ClosedAt, shift, ih₁, ih₂]
  | proj b e ih =>
      simp [ClosedAt, shift, ih]
  | op o e₁ e₂ ih₁ ih₂ =>
      simp [ClosedAt, shift, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      simp [ClosedAt, shift, ih₀, ih₁, ih₂]
  | letE e₁ e₂ ih₁ ih₂ =>
      simp [ClosedAt, shift, ih₁, ih₂]
  | omega => simp [ClosedAt, shift]
  | err => simp [ClosedAt, shift]

/-- Shifting a term below a cutoff has no effect when the term contains only
variables bound below that cutoff. -/
theorem shift_eq_of_closedAt {d amount : Nat} {e : Term}
    (h : ClosedAt d e) : shift amount d e = e := by
  induction e generalizing d amount with
  | var i =>
      simp only [ClosedAt] at h
      simp [shift, Nat.not_le_of_gt h]
  | int n => rfl
  | lam body ih =>
      simp only [ClosedAt] at h
      simp [shift, ih h]
  | fix body ih =>
      simp only [ClosedAt] at h
      simp [shift, ih h]
  | app e₁ e₂ ih₁ ih₂ =>
      simp only [ClosedAt] at h
      simp [shift, ih₁ h.1, ih₂ h.2]
  | pair e₁ e₂ ih₁ ih₂ =>
      simp only [ClosedAt] at h
      simp [shift, ih₁ h.1, ih₂ h.2]
  | proj b e ih =>
      simp only [ClosedAt] at h
      simp [shift, ih h]
  | op o e₁ e₂ ih₁ ih₂ =>
      simp only [ClosedAt] at h
      simp [shift, ih₁ h.1, ih₂ h.2]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      simp only [ClosedAt] at h
      simp [shift, ih₀ h.1, ih₁ h.2.1, ih₂ h.2.2]
  | letE e₁ e₂ ih₁ ih₂ =>
      simp only [ClosedAt] at h
      simp [shift, ih₁ h.1, ih₂ h.2]
  | omega => rfl
  | err => rfl

/-- Shifting a closed term at the top level has no effect. -/
theorem shift_eq_of_closed {amount : Nat} {e : Term}
    (h : Closed e) : shift amount 0 e = e := by
  exact shift_eq_of_closedAt h


theorem nat_not_eq_of_lt {a b : Nat} : a < b → ¬a = b := by
    intro h h_eq
    exact  Nat.ne_of_lt h h_eq

/-- Substitution at a free-variable position has no effect on a term whose
free variables are all below that position. -/
theorem subst_eq_of_closedAt {d j : Nat} {s e : Term}
    (hClosed : ClosedAt d e) (hDj : d ≤ j) :
    subst j s e = e := by
  induction e generalizing d j s with
  | var i =>
      simp only [ClosedAt] at hClosed
      simp_all [subst]
      have hij : i < j := Nat.lt_of_lt_of_le hClosed hDj
      simp [Nat.not_lt_of_ge (Nat.le_of_lt hij), nat_not_eq_of_lt hij]
  | int n => rfl
  | lam body ih =>
      simp only [ClosedAt] at hClosed
      rw [subst]
      congr 1
      apply ih hClosed
      exact Nat.succ_le_succ hDj
  | fix body ih =>
      simp only [ClosedAt] at hClosed
      rw [subst]
      congr 1
      apply ih hClosed
      exact Nat.succ_le_succ hDj
  | app e₁ e₂ ih₁ ih₂ =>
      simp [subst, ih₁ hClosed.1 hDj, ih₂ hClosed.2 hDj]
  | pair e₁ e₂ ih₁ ih₂ =>
      simp [subst, ih₁ hClosed.1 hDj, ih₂ hClosed.2 hDj]
  | proj b e ih =>
      simp [subst, ih hClosed hDj]
  | op o e₁ e₂ ih₁ ih₂ =>
      simp [subst, ih₁ hClosed.1 hDj, ih₂ hClosed.2 hDj]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      simp [subst, ih₀ hClosed.1 hDj, ih₁ hClosed.2.1 hDj, ih₂ hClosed.2.2 hDj]
  | letE e₁ e₂ ih₁ ih₂ =>
      simp only [ClosedAt] at hClosed
      rw [subst]
      congr 2
      · exact ih₁ hClosed.1 hDj
      · apply ih₂ hClosed.2
        exact Nat.succ_le_succ hDj
  | omega => rfl
  | err => rfl

/-- A top-level unit shift preserves closedness. -/
theorem closed_shift_iff {e : Term} :
    Closed (shift 1 0 e) ↔ Closed e := by
  simpa [Closed] using (closedAt_shift_iff (d := 0) (amount := 1) (e := e))

end Term

end Strictness
