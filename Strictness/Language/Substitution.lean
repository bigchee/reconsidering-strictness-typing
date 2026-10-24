import Strictness.Language.Syntax

namespace Strictness

open Term

/-- A semantic substitution maps every free De Bruijn variable to a term.
The terms substituted for variables are intended to be closed. -/
abbrev Substitution := Nat → Term

namespace Substitution

/-- Shift every substituted term when the substitution crosses a binder. -/
def lift (ρ : Substitution) : Substitution := fun i => Term.shift 1 0 (ρ i)

/-- Apply a substitution at a given binder depth.
Bound variables are preserved; free variables are replaced by shifted images. -/
def applyAt (ρ : Substitution) (depth : Nat) : Term → Term
  | .var i =>
      if i < depth then .var i
      else Term.shift depth 0 (ρ (i - depth))
  | .int n => .int n
  | .lam body => .lam (applyAt ρ (depth + 1) body)
  | .fix body => .fix (applyAt ρ (depth + 1) body)
  | .app e₁ e₂ => .app (applyAt ρ depth e₁) (applyAt ρ depth e₂)
  | .pair e₁ e₂ => .pair (applyAt ρ depth e₁) (applyAt ρ depth e₂)
  | .proj b e => .proj b (applyAt ρ depth e)
  | .op o e₁ e₂ => .op o (applyAt ρ depth e₁) (applyAt ρ depth e₂)
  | .ite e₀ e₁ e₂ =>
      .ite (applyAt ρ depth e₀) (applyAt ρ depth e₁) (applyAt ρ depth e₂)
  | .letE e₁ e₂ =>
      .letE (applyAt ρ depth e₁) (applyAt ρ (depth + 1) e₂)
  | .omega => .omega
  | .err => .err

/-- Apply a substitution at the top level. -/
def apply (ρ : Substitution) (e : Term) : Term := applyAt ρ 0 e

@[simp] theorem apply_var (ρ : Substitution) (i : Nat) :
    apply ρ (.var i) = ρ i := by
      simp [apply, applyAt]

@[simp] theorem apply_int (ρ : Substitution) (n : Int) :
    apply ρ (.int n) = .int n := rfl

@[simp] theorem apply_lam (ρ : Substitution) (body : Term) :
    apply ρ (.lam body) = .lam (applyAt ρ 1 body) := rfl

@[simp] theorem apply_fix (ρ : Substitution) (body : Term) :
    apply ρ (.fix body) = .fix (applyAt ρ 1 body) := rfl

@[simp] theorem apply_pair (ρ : Substitution) (e₁ e₂ : Term) :
    apply ρ (.pair e₁ e₂) = .pair (apply ρ e₁) (apply ρ e₂) := rfl

/-- Extend a semantic substitution with an argument for the newest binder. -/
def extend (ρ : Substitution) (a : Term) : Substitution :=
  fun i => if i = 0 then a else Term.shift 1 0 (ρ (i - 1))

@[simp] theorem extend_zero (ρ : Substitution) (a : Term) :
    extend ρ a 0 = a := by simp [extend]

/-- When a substitution argument is closed, shifting it preserves its value up to
being placed under the newly introduced binder. -/
theorem apply_var_at_depth (ρ : Substitution) (depth i : Nat)
    (h : i < depth) :
    applyAt ρ depth (.var i) = .var i := by
  simp [applyAt, h]

/-- Closed substitution images remain closed after extension. -/
theorem extend_closed (ρ : Substitution) (a : Term)
    (hρ : ∀ i, Term.Closed (ρ i)) (ha : Term.Closed a) :
    ∀ i, Term.Closed (extend ρ a i) := by
  intro i
  cases i with
  | zero => simpa using ha
  | succ i =>
      simp [extend, Term.closed_shift_iff, hρ i]

/-- A De Bruijn beta-substitution commutation lemma.  For closed semantic
substitution images, extending the substitution by a closed argument and
then applying it is the same as closing the body and beta-substituting the
argument. -/
theorem applyAt_extend_eq_subst_of_closed
    (ρ : Substitution) (a : Term)
    (hρ : ∀ i, Term.Closed (ρ i)) (ha : Term.Closed a) :
    ∀ d e,
      applyAt (extend ρ a) d e =
        Term.subst d (Term.shift d 0 a) (applyAt ρ (d + 1) e)
  | d, .var i => by
      by_cases hlt : i < d
      · have hne : i ≠ d := Nat.ne_of_lt hlt
        have hnot : ¬ d < i := Nat.not_lt_of_ge (Nat.le_of_lt hlt)
        have hlt' : i < d + 1 := by
          simpa [Nat.succ_eq_add_one] using Nat.lt_succ_of_lt hlt
        simp [applyAt, hlt, hlt', Term.subst, hne, hnot]
      · by_cases heq : i = d
        · subst i
          simp [applyAt, Term.subst]
        · have hdi : d < i := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
          obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hdi)
          cases j with
          | zero => contradiction
          | succ j =>
              have hc := hρ j
              have hc := hρ j
              have hidx : d + (j + 1) - (d + 1) = j := by
                omega
              simp only [applyAt, extend]
              simp [hlt, hidx,
                Term.shift_eq_of_closed hc,
                Term.subst_eq_of_closedAt hc (Nat.zero_le d)]
  | d, .int n => rfl
  | d, .lam body => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha (d + 1) body]
      congr 1
      simp [Term.shift_eq_of_closed ha]
  | d, .fix body => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha (d + 1) body]
      congr 1
      simp [Term.shift_eq_of_closed ha]
  | d, .app e₁ e₂ => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₁,
        applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₂]
  | d, .pair e₁ e₂ => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₁,
        applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₂]
  | d, .proj b e => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha d e]
  | d, .op o e₁ e₂ => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₁,
        applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₂]
  | d, .ite e₀ e₁ e₂ => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₀,
        applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₁,
        applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₂]
  | d, .letE e₁ e₂ => by
      simp only [applyAt, Term.subst]
      rw [applyAt_extend_eq_subst_of_closed ρ a hρ ha d e₁,
        applyAt_extend_eq_subst_of_closed ρ a hρ ha (d + 1) e₂]
      congr 1
      have h₁ : Term.shift (d + 1) 0 a = a :=
        Term.shift_eq_of_closed ha
      have h₂ : Term.shift 1 0 (Term.shift d 0 a) = a := by
        rw [Term.shift_eq_of_closed ha]
        exact Term.shift_eq_of_closed ha
      rw [h₁, h₂]
  | _, .omega => rfl
  | _, .err => rfl

/-- The top-level beta form of the commutation lemma. -/
theorem apply_extend_eq_instantiate_of_closed
    (ρ : Substitution) (a e : Term)
    (hρ : ∀ i, Term.Closed (ρ i)) (ha : Term.Closed a) :
    apply (extend ρ a) e =
      Term.instantiate (applyAt ρ 1 e) a := by
  simpa [apply, Term.instantiate] using
    applyAt_extend_eq_subst_of_closed ρ a hρ ha 0 e

end Substitution

end Strictness

namespace Strictness

/-- A constant semantic substitution used for the one-free-variable
observational soundness corollaries.  For a single-variable typing context only index 0
is relevant; all indices are nevertheless mapped to the same closed term so
that `ClosedSubstitution` is immediate. -/
def singleSubst (a : Term) : Substitution := fun _ => a

@[simp] theorem singleSubst_apply (a e : Term) :
    Substitution.apply (singleSubst a) e = Substitution.apply (fun _ => a) e := rfl

end Strictness
