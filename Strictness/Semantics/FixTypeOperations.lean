import Strictness.Semantics.SemanticSubtype

namespace Strictness

/-- V ignores the distinction between outer ?/S and between outer L/top. -/
theorem V_raiseStrict (τ : Ty) :
    V (Ty.raiseStrict τ) = V τ := by
  cases τ with
  | int u =>
      cases u <;>
        simp [Ty.raiseStrict, Ty.outer, Ty.reannotate, Usage.join,
          V, LogicalModel.acceptable, Usage.Le]
  | prod σ τ u =>
      cases u <;>
        simp [Ty.raiseStrict, Ty.outer, Ty.reannotate, Usage.join,
          V, LogicalModel.acceptable, Usage.Le]
  | arrow σ τ u =>
      cases u <;>
        simp [Ty.raiseStrict, Ty.outer, Ty.reannotate, Usage.join,
          V, LogicalModel.acceptable, Usage.Le]

end Strictness
