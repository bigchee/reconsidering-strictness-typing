import Strictness.Semantics.SemanticLemmas
import Strictness.Language.Substitution
import Strictness.Language.Environment

namespace Strictness

open Term

/-- In the source methodology an expression environment maps variables to
closed expressions.  We keep the underlying substitution as a plain function
and record this closure property explicitly. -/
def ClosedSubstitution (ρ : Substitution) : Prop :=
  ∀ i, Term.Closed (ρ i)

/-- A substitution is V-valid for an environment.  The closure component
mirrors Smetsers--van Eekelen's `ρ : V → Λ₀`; the second component is the
interpretation-specific membership condition. -/
def Valid (Γ : Env) (ρ : Substitution) : Prop :=
  ClosedSubstitution ρ ∧
  ∀ i τ, Env.lookup Γ i = some τ → V τ (ρ i)

/-- A substitution satisfies the D-side environment condition when some
variable image belongs to the corresponding D-set. -/
def SatisfiesD (Γ : Env) (ρ : Substitution) : Prop :=
  ∃ i τ, Env.lookup Γ i = some τ ∧ D τ (ρ i)

/-- A substitution maps every variable to a closed term of its erased simple
 type for every declaration in the environment. -/
def SimpleValid (Γ : Env) (ρ : Substitution) : Prop :=
  ∀ i τ, Env.lookup Γ i = some τ → AllTerms τ.erase (ρ i)

@[simp] theorem closedSubstitution_shift_tail {ρ : Substitution}
    (hρ : ClosedSubstitution ρ) :
    ClosedSubstitution (fun i => Term.shift 1 0 (ρ (i + 1))) := by
  intro i
  simpa [Term.closed_shift_iff] using hρ (i + 1)

/-- The empty environment is satisfied by no D-witness. -/
theorem not_satisfiesD_nil {ρ : Substitution} : ¬ SatisfiesD [] ρ := by
  rintro ⟨i, τ, h, _⟩
  cases h

/-- Validity of an extended environment decomposes into closure, the newest
binder image, and the shifted tail substitution. -/
theorem valid_cons_iff {σ : Ty} {Γ : Env} {ρ : Substitution} :
    Valid (σ :: Γ) ρ ↔
      ClosedSubstitution ρ ∧
      V σ (ρ 0) ∧
      Valid Γ (fun i => Term.shift 1 0 (ρ (i + 1))) := by
  constructor
  · intro h
    refine ⟨h.1, h.2 0 σ rfl, ?_⟩
    refine ⟨closedSubstitution_shift_tail h.1, ?_⟩
    intro i τ hi
    have hV := h.2 (i + 1) τ hi
    have hClosed : Term.Closed (ρ (i + 1)) := h.1 (i + 1)
    simpa [Term.shift_eq_of_closed hClosed] using hV
  · rintro ⟨hClosed, hσ, hΓ⟩
    refine ⟨hClosed, ?_⟩
    intro i τ hi
    cases i with
    | zero =>
        simp only [Env.lookup] at hi
        cases hi
        exact hσ
    | succ i =>
        have hV := hΓ.2 i τ hi
        have hc := hClosed (i + 1)
        simpa [Term.shift_eq_of_closed hc] using hV

/-- Satisfaction decomposes into the newest binding or the shifted tail. -/
theorem satisfiesD_cons_iff {σ : Ty} {Γ : Env} {ρ : Substitution} :
    SatisfiesD (σ :: Γ) ρ ↔
      D σ (ρ 0) ∨
      SatisfiesD Γ (fun i => Term.shift 1 0 (ρ (i + 1))) := by
  constructor
  · rintro ⟨i, τ, hi, hD⟩
    cases i with
    | zero =>
        left
        simp only [Env.lookup] at hi
        cases hi
        exact hD
    | succ i =>
        right
        have hClosed : Term.Closed (ρ (i + 1)) := D_closed hD
        refine ⟨i, τ, hi, ?_⟩
        simpa [Term.shift_eq_of_closed hClosed] using hD
  · intro h
    cases h with
    | inl hσ => exact ⟨0, σ, rfl, hσ⟩
    | inr hΓ =>
        rcases hΓ with ⟨i, τ, hi, hD⟩
        have hClosedShift : Term.Closed (Term.shift 1 0 (ρ (i + 1))) := D_closed hD
        have hClosed : Term.Closed (ρ (i + 1)) :=
          (Term.closed_shift_iff).mp hClosedShift
        refine ⟨i + 1, τ, hi, ?_⟩
        simpa [Term.shift_eq_of_closed hClosed] using hD

/-- Simple validity has the same De Bruijn tail adjustment. -/
theorem simpleValid_cons_iff {σ : Ty} {Γ : Env} {ρ : Substitution} :
    SimpleValid (σ :: Γ) ρ ↔
      AllTerms σ.erase (ρ 0) ∧
      SimpleValid Γ (fun i => Term.shift 1 0 (ρ (i + 1))) := by
  constructor
  · intro h
    constructor
    · exact h 0 σ rfl
    · intro i τ hi
      have hT := h (i + 1) τ hi
      have hClosed : Term.Closed (ρ (i + 1)) := hT.1
      simpa [Term.shift_eq_of_closed hClosed] using hT
  · rintro ⟨hσ, hΓ⟩ i τ hi
    cases i with
    | zero =>
        simp only [Env.lookup] at hi
        cases hi
        exact hσ
    | succ i =>
        have hT := hΓ i τ hi
        have hClosedShift : Term.Closed (Term.shift 1 0 (ρ (i + 1))) := hT.1
        have hClosed : Term.Closed (ρ (i + 1)) :=
          (Term.closed_shift_iff).mp hClosedShift
        simpa [Term.shift_eq_of_closed hClosed] using hT

end Strictness
