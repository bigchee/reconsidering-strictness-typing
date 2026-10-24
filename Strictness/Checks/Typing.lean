import Strictness.Inference.Correspondence

/-!
Concrete typing and constraint-generation checks.

Covers raising, self and nested recursion, and independently annotated
function types. These checks are built separately from the main library.
-/


namespace Strictness


open Usage

/-- Raising permits S <= raiseStrict(?), while S <= ? fails. -/
theorem strict_to_unknown_raising_comparison :
    Ty.Subtype (.int strict) (Ty.raiseStrict (.int unknown)) ∧
      ¬ Ty.Subtype (.int strict) (.int unknown) := by
  constructor
  · exact Ty.Subtype.int (by trivial)
  · intro h
    cases h with
    | int hUse => exact hUse

/-- The recursive variable has type Int^?, while the body/result has Int^S. -/
theorem typing_fix_self_via_raising :
    Typing [] (.fix (.var 0)) (.int strict) := by
  have hVar : Typing [.int unknown] (.var 0) (.int unknown) :=
    Typing.var (Γ := []) (τ := .int unknown) (by trivial)
  have hRefl : Ty.Subtype (.int unknown) (.int unknown) :=
    Ty.Subtype.int (by trivial)
  have hUp : Ty.Subtype (.int unknown) (.int strict) :=
    Ty.Subtype.int (by trivial)
  have hEnv : Env.Subtype [.int unknown] [.int unknown] :=
    ⟨hRefl, True.intro⟩
  have hBody : Typing [.int unknown] (.var 0) (.int strict) :=
    Typing.sub hVar hEnv hUp
  exact Typing.fix (Γ := []) (σ := .int unknown) hBody
    strict_to_unknown_raising_comparison.1 rfl

/-- The fix context changes both unused L entries to top. -/
theorem typing_fix_self_two_top :
    Typing [.int top, .int top] (.fix (.var 0)) (.int strict) := by
  have hBody :
      Typing [.int strict, .int lazy, .int lazy] (.var 0) (.int strict) :=
    Typing.var (Γ := [.int lazy, .int lazy]) (τ := .int strict)
      (by simp [Env.IsLazy, Ty.IsLazy, Usage.Le])
  have hSub : Ty.Subtype (.int strict) (Ty.raiseStrict (.int strict)) :=
    Ty.Subtype.int (by trivial)
  exact Typing.fix (Γ := [.int lazy, .int lazy]) (σ := .int strict)
    hBody hSub rfl


end Strictness

namespace Strictness


open Usage
open RawInference.CoreBoundary

/-- Both fix nodes must be handled; the inner fix changes its free context to top. -/
theorem typing_nested_fix :
    Typing [] (.fix (.fix (.var 0))) (.int strict) := by
  have hv : Typing [.int strict, .int lazy] (.var 0) (.int strict) :=
    Typing.var (Γ := [.int lazy]) (τ := .int strict) (by trivial)
  have hi : Typing [.int top] (.fix (.var 0)) (.int strict) :=
    Typing.fix hv (Ty.Subtype.int (by trivial)) rfl
  exact Typing.fix hi (Ty.Subtype.int (by trivial)) rfl

/-- Concrete raising example has a satisfiable, variable-left constraint set. -/
theorem fix_self_generated :
    ∃ G T C ν,
      Derives G (.fix (.var 0)) T C ∧
      VariableDefinite C ∧ C.DualDefinite ∧ C.Satisfies ν ∧
      Raw.Env.eval ν G = [] ∧ T.eval ν = .int strict := by
  obtain ⟨G, T, C, ν, hd, hs, hG, hT⟩ :=
    typing_complete typing_fix_self_via_raising
  exact ⟨G, T, C, ν, hd, hd.constraints_variableDefinite,
    hd.constraints_dualDefinite, hs, hG, hT⟩

/-- Completeness and the constraint-shape proof also cover nested fix nodes. -/
theorem nested_fix_generated :
    ∃ G T C ν,
      Derives G (.fix (.fix (.var 0))) T C ∧
      C.DualDefinite ∧ C.Satisfies ν ∧
      Raw.Env.eval ν G = [] ∧ T.eval ν = .int strict :=
  typing_correspondence_dualDefinite.mp typing_nested_fix


end Strictness

namespace Strictness


open Usage

/-- The root and codomain annotations of a variable's arrow type are independent. -/
def testArrow : Ty := .arrow (.int unknown) (.int lazy) top

theorem typing_variable_arbitrary_arrow :
    Typing [testArrow] (.var 0) testArrow :=
  Typing.var (Γ := []) (τ := testArrow) (by trivial)

/-- The same judgment has a satisfied constraint derivation in the certified form. -/
theorem arbitrary_arrow_generated :
    ∃ G T C ν,
      RawInference.CoreBoundary.Derives G (.var 0) T C ∧
      C.DualDefinite ∧ C.Satisfies ν ∧
      Raw.Env.eval ν G = [testArrow] ∧ T.eval ν = testArrow :=
  RawInference.CoreBoundary.typing_correspondence_dualDefinite.mp
    typing_variable_arbitrary_arrow


end Strictness
