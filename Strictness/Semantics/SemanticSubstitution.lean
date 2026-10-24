import Strictness.Semantics.SemanticEnvironment
import Strictness.Semantics.SemanticBasic
import Strictness.Language.SimpleSubstitution

namespace Strictness

open Usage
open Term

/-- A Lazy environment has no D-witness.  This is the environment-level
form of `Lazy(τ) -> D(τ) = ∅` and does not depend on the typing induction. -/
theorem not_satisfiesD_of_lazy {Γ : Env} {ρ : Substitution}
    (hLazy : Env.IsLazy Γ) : ¬ SatisfiesD Γ ρ := by
  intro hD
  rcases hD with ⟨i, τ, hi, hτ⟩
  induction Γ generalizing i τ ρ with
  | nil => simp [Env.lookup] at hi
  | cons σ Γ ih =>
      cases i with
      | zero =>
          simp only [Env.lookup] at hi
          cases hi
          rw [lazy_implies_D_empty hLazy.1] at hτ
          exact hτ
      | succ i =>
          simp only [Env.lookup] at hi
          exact ih (ρ := fun j => ρ (j + 1)) (i := i) (τ := τ)
            hLazy.2 hi hτ

/-- A V-valid substitution for a scaled `?` or `S` environment is valid for
its unscaled environment.  These are precisely the nontrivial scaling cases
needed by T-Abs and T-App. -/
theorem valid_of_unknown_scale {Γ : Env} {ρ : Substitution}
    (h : Valid (Env.scale unknown Γ) ρ) : Valid Γ ρ := by
  refine ⟨h.1, ?_⟩
  intro i τ hi
  have hscaled := h.2 i (Ty.scale unknown τ) (Env.lookup_scale hi)
  simpa [LogicalModel.acceptable_unknown_scale] using hscaled

theorem valid_of_strict_scale {Γ : Env} {ρ : Substitution}
    (h : Valid (Env.scale strict Γ) ρ) : Valid Γ ρ := by
  refine ⟨h.1, ?_⟩
  simpa [Ty.strict_scale] using h.2

/-- A V-valid substitution yields a simply typed, closed image for every
binding. -/
theorem Valid.simpleValid {Γ : Env} {ρ : Substitution}
    (h : Valid Γ ρ) : SimpleValid Γ ρ := by
  intro i τ hi
  exact V_subset_allTerms τ (h.2 i τ hi)

/-- A V-valid substitution yields a closed simply typed image for every
position in the erased simple context. -/
theorem Valid.simpleValid_erased {Γ : Env} {ρ : Substitution}
    (h : Valid Γ ρ) :
    ∀ i τ, Term.lookup (Env.erase Γ) i = some τ → AllTerms τ (ρ i) := by
  intro i τ hi
  rcases Env.erase_lookup_iff.mp hi with ⟨σ, hσ, hEq⟩
  have hAll := V_subset_allTerms σ (h.2 i σ hσ)
  simpa [hEq] using hAll

/-- Extending a valid substitution by a V-member for the newest binding is
valid for the extended environment. -/
theorem valid_extend_head {σ : Ty} {Γ : Env} {ρ : Substitution} {a : Term}
    (ha : V σ a) (hρ : Valid Γ ρ) :
    Valid (σ :: Γ) (Substitution.extend ρ a) := by
  rw [valid_cons_iff]
  refine ⟨?_, ha, ?_⟩
  · have hExtClosed := Substitution.extend_closed ρ a hρ.1 (V_closed ha)
    exact hExtClosed
  · refine ⟨?_, ?_⟩
    · apply closedSubstitution_shift_tail
      exact Substitution.extend_closed ρ a hρ.1 (V_closed ha)
    intro i τ hi
    have hV := hρ.2 i τ hi
    have hClosed := hρ.1 i
    simpa [Substitution.extend, Term.shift_eq_of_closed hClosed] using hV

/-- A head D-member is enough to make an extended substitution satisfy the
D-side environment condition. -/
theorem satisfiesD_extend_head {σ : Ty} {Γ : Env} {ρ : Substitution} {a : Term}
    (ha : D σ a) : SatisfiesD (σ :: Γ) (Substitution.extend ρ a) := by
  exact ⟨0, σ, rfl, by simpa using ha⟩

/-- A D-witness in the tail can also be transported through substitution
extension by any closed or non-closed head term, because the witnessed image
itself is the tail image and is closed. -/
theorem satisfiesD_extend_tail {σ : Ty} {Γ : Env} {ρ : Substitution} {a : Term}
    (hρ : SatisfiesD Γ ρ) :
    SatisfiesD (σ :: Γ) (Substitution.extend ρ a) := by
  rcases hρ with ⟨i, τ, hi, hD⟩
  have hc := D_closed hD
  refine ⟨i + 1, τ, hi, ?_⟩
  simpa [Substitution.extend, Term.shift_eq_of_closed hc] using hD

end Strictness
