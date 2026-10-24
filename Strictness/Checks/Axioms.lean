import Strictness

/-!
Signatures and axiom dependencies of the principal public results.

`#print axioms` reports dependencies for inspection; compiling this file alone
does not enforce an allowlist. The concrete typing checks live separately.
-/

#check Strictness.Typing.fix
#print axioms Strictness.V_raiseStrict
#print axioms Strictness.semantic_unfold_admissible
#print axioms Strictness.fixApprox_mem_V_limit
#print axioms Strictness.fixApprox_mem_D_of_cofinal
#print axioms Strictness.fundamental_fix_of_simpleTyping
#print axioms Strictness.fundamental
#print axioms Strictness.fix_self_diverges
#check Strictness.RawInference.CoreBoundary.Rule.fix
#check Strictness.RawInference.CoreBoundary.Derives.constraints_variableDefinite
#check Strictness.RawInference.CoreBoundary.Derives.constraints_dualDefinite
#check Strictness.RawInference.CoreBoundary.typing_buildable
#check Strictness.RawInference.CoreBoundary.typing_complete
#check Strictness.RawInference.CoreBoundary.typing_correspondence
#print axioms Strictness.RawInference.CoreBoundary.buildable_fix
#print axioms Strictness.RawInference.CoreBoundary.typing_correspondence_dualDefinite
#print axioms Strictness.RawInference.CoreBoundary.Derives.constraints_variableDefinite
#print axioms Strictness.RawInference.CoreBoundary.Derives.constraints_dualDefinite
#print axioms Strictness.RawInference.CoreBoundary.Derives.toTyping
#print axioms Strictness.V_op
#print axioms Strictness.D_op_left
#print axioms Strictness.D_op_right
#print axioms Strictness.top_open_smallStep
#check Strictness.Typing
#check Strictness.Ty.Subtype
#check Strictness.Env.Subtype
#check Strictness.typing_erasure
#check Strictness.fundamental
#check Strictness.strict_smallStep_terminal_demands
#check Strictness.lazy_smallStep
#check Strictness.top_open_smallStep
#print axioms Strictness.strict_smallStep_terminal_demands
#print axioms Strictness.lazy_smallStep
#print axioms Strictness.top_open_infiniteSteps
#print axioms Strictness.top_smallStep
#print axioms Strictness.demanded_smallStep_terminal
