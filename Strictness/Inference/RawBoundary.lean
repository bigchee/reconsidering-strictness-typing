import Strictness.Inference.RawInference

/-! Structural type and context composition for symbolic annotations.
Function interiors generate equality constraints; product components are
composed recursively. These operations are shared by the generator and its
soundness, constraint-shape, allocation, and completeness proofs. -/

namespace Strictness.RawInference.Boundary

open Raw

abbrev RTy := Raw.Ty
abbrev REnv := Raw.Env
abbrev UC := Raw.UseConstraints

/-- Equality of function interiors is a usage obligation, not a hidden
valuation-dependent shape check. Skeleton mismatch returns none. -/
noncomputable def equalTypes (A B : RTy) : Option UC := do
  let C ← A.subtypeConstraints B
  let D ← B.subtypeConstraints A
  pure (C ++ D)

inductive CombineOp where
  | plus | cap
  deriving DecidableEq

def CombineOp.expr : CombineOp → Raw.Expr → Raw.Expr → Raw.Expr
  | .plus => .add
  | .cap => .meet

def CombineOp.usage : CombineOp → Usage → Usage → Usage
  | .plus => Usage.add
  | .cap => Usage.meet

/-- Unlike Raw.Ty.combine, different variable names inside matching arrows
are accepted and their equality is emitted as constraints. -/
noncomputable def composeTy (op : CombineOp) : RTy → RTy → Option (RTy × UC)
  | .int u, .int v => some (.int (op.expr u v), [])
  | .prod A B u, .prod A' B' v => do
      let (D, C₁) ← composeTy op A A'
      let (F, C₂) ← composeTy op B B'
      pure (.prod D F (op.expr u v), C₁ ++ C₂)
  | .arrow A B u, .arrow A' B' v => do
      let C₁ ← equalTypes A A'
      let C₂ ← equalTypes B B'
      pure (.arrow A B (op.expr u v), C₁ ++ C₂)
  | _, _ => none

noncomputable def composeEnv (op : CombineOp) : REnv → REnv → Option (REnv × UC)
  | [], [] => some ([], [])
  | A :: Γ, B :: Δ => do
      let (D, C₁) ← composeTy op A B
      let (Ξ, C₂) ← composeEnv op Γ Δ
      pure (D :: Ξ, C₁ ++ C₂)
  | _, _ => none

end Strictness.RawInference.Boundary
