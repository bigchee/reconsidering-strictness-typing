import Strictness.Compatibility.Omega.Semantics
import Strictness.Semantics.FixApproximation

/-!
Finite approximations using the source-language loop.

Expanding internal finite approximations gives exactly the recurrence whose
initial term is `.fix (.var 0)`. For `OmegaFree` bodies the body is unchanged.
Membership in both interpretations agrees at every depth; this includes
depths where neither initial loop belongs to a particular D-set.
-/

namespace Strictness
namespace Term

/-- Translating internal approximations gives source-loop approximations exactly. -/
theorem expandOmega_fixApprox (body : Term) (n : Nat) :
    (fixApprox body n).expandOmega = sourceFixApprox body.expandOmega n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fixApprox, sourceFixApprox, expandOmega_instantiate, ih]

theorem fixApprox_omegaEq_source (body : Term) (n : Nat) :
    OmegaEq (fixApprox body n) (sourceFixApprox body.expandOmega n) := by
  rw [← expandOmega_fixApprox]
  exact omegaEq_expandOmega _

/-- For bodies from the source fragment, the body itself is unchanged. -/
theorem fixApprox_omegaEq_source_of_omegaFree {body : Term}
    (h : OmegaFree body) (n : Nat) :
    OmegaEq (fixApprox body n) (sourceFixApprox body n) := by
  simpa only [expandOmega_eq_of_omegaFree h] using fixApprox_omegaEq_source body n

end Term

theorem fixApprox_source_semantic_VD (body : Term) (n : Nat) (τ : Ty) :
    (V τ (Term.fixApprox body n) ↔ V τ (Term.sourceFixApprox body.expandOmega n)) ∧
    (D τ (Term.fixApprox body n) ↔ D τ (Term.sourceFixApprox body.expandOmega n)) :=
  omegaEq_semantic_VD (Term.fixApprox_omegaEq_source body n) τ

theorem fixApprox_source_smallStep_VD (body : Term) (n : Nat) (τ : Ty) :
    (SmallStep.V τ (Term.fixApprox body n) ↔
      SmallStep.V τ (Term.sourceFixApprox body.expandOmega n)) ∧
    (SmallStep.D τ (Term.fixApprox body n) ↔
      SmallStep.D τ (Term.sourceFixApprox body.expandOmega n)) := by
  rw [SmallStep.V_eq, SmallStep.D_eq]
  exact fixApprox_source_semantic_VD body n τ

end Strictness
