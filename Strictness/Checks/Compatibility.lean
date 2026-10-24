import Strictness.Compatibility.Omega.Approximation
import Strictness.Compatibility.Semantics

/-!
Axiom dependencies of the observation and representation bridges.

Includes equality of type interpretations and source-loop approximations.
Like the main axiom check, these commands report rather than restrict axioms.
-/

#print axioms Strictness.eval_iff_steps_value
#print axioms Strictness.evalErr_iff_steps_error
#print axioms Strictness.step_deterministic
#print axioms Strictness.value_smallStep_terminal
#print axioms Strictness.evalCtx_err_smallStep_terminal
#print axioms Strictness.steps_closed_typed
#print axioms Strictness.closed_typed_progress
#print axioms Strictness.infiniteSteps_diverges
#print axioms Strictness.diverges_iff_infiniteSteps
#print axioms Strictness.SmallStep.divergentTerms_eq
#print axioms Strictness.SmallStep.numeralTerms_eq
#print axioms Strictness.SmallStep.pairTerms_eq
#print axioms Strictness.SmallStep.functionTerms_eq
#print axioms Strictness.SmallStep.strictFunctionTerms_eq
#print axioms Strictness.SmallStep.model_eq
#print axioms Strictness.SmallStep.V_eq
#print axioms Strictness.SmallStep.D_eq
#print axioms Strictness.Term.OmegaEq.instantiate
#print axioms Strictness.Term.OmegaEq.hasType
#print axioms Strictness.Term.OmegaEq.closedAt
#print axioms Strictness.Term.omegaEq_expandOmega
#print axioms Strictness.Term.expandOmega_omegaFree
#print axioms Strictness.Term.expandOmega_hasType_iff
#print axioms Strictness.Term.expandOmega_instantiate
#print axioms Strictness.Substitution.expandOmega_apply
#print axioms Strictness.eval_expandOmega_iff
#print axioms Strictness.evalErr_expandOmega_iff
#print axioms Strictness.steps_value_expandOmega_iff
#print axioms Strictness.steps_error_expandOmega_iff
#print axioms Strictness.infiniteSteps_expandOmega_iff
#print axioms Strictness.omega_semEq_fix_self
#print axioms Strictness.omegaEq_semantic_VD
#print axioms Strictness.expandOmega_smallStep_VD
#print axioms Strictness.Term.expandOmega_fixApprox
#print axioms Strictness.Term.fixApprox_omegaEq_source_of_omegaFree
#print axioms Strictness.fixApprox_source_smallStep_VD
