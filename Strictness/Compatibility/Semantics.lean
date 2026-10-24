import Strictness.Semantics.SmallStep
import Strictness.Compatibility.Operational

/-!
Equality of the big-step and small-step type interpretations.

Replaces each big-step observation in the logical-model operations using
operational correspondence. Equality of the complete models transports both
mutually recursive interpretations, so the existing fundamental lemma also
establishes membership in the small-step interpretation.
-/

namespace Strictness.SmallStep

theorem divergentTerms_eq (A : SimpleTy) :
    DivergentTerms A = Strictness.DivergentTerms A := by
  funext e
  apply propext
  constructor
  · rintro ⟨hAll, hInf⟩
    exact ⟨hAll, infiniteSteps_diverges hInf⟩
  · rintro ⟨hAll, hDiv⟩
    exact ⟨hAll, diverges_infiniteSteps hAll.2 hDiv⟩

theorem numeralTerms_eq : NumeralTerms = Strictness.NumeralTerms := by
  funext e
  apply propext
  simp only [NumeralTerms, Strictness.NumeralTerms, eval_iff_steps_value, Value.toTerm]

theorem pairTerms_eq (σ τ : SimpleTy) (X Y : TermSet Term) :
    PairTerms σ τ X Y = Strictness.PairTerms σ τ X Y := by
  funext e
  apply propext
  simp only [PairTerms, Strictness.PairTerms, eval_iff_steps_value, Value.toTerm]

theorem functionTerms_eq (σ τ : SimpleTy) (VX DX VY DY : TermSet Term) :
    FunctionTerms σ τ VX DX VY DY = Strictness.FunctionTerms σ τ VX DX VY DY := by
  funext e
  apply propext
  simp only [FunctionTerms, Strictness.FunctionTerms, eval_iff_steps_value, Value.toTerm]

theorem strictFunctionTerms_eq (σ τ : SimpleTy) (VArrow VX DY : TermSet Term) :
    StrictFunctionTerms σ τ VArrow VX DY = Strictness.StrictFunctionTerms σ τ VArrow VX DY := by
  funext e
  apply propext
  simp only [StrictFunctionTerms, Strictness.StrictFunctionTerms,
    eval_iff_steps_value, Value.toTerm]

/-- Equality of the complete models also transports the mutually recursive interpretations. -/
theorem model_eq : model = operationalModel := by
  have hDiv : DivergentTerms = Strictness.DivergentTerms := funext divergentTerms_eq
  have hPair : PairTerms = Strictness.PairTerms :=
    funext fun σ => funext fun τ => funext fun X => funext fun Y => pairTerms_eq σ τ X Y
  have hFun : FunctionTerms = Strictness.FunctionTerms :=
    funext fun σ => funext fun τ => funext fun VX => funext fun DX =>
      funext fun VY => funext fun DY => functionTerms_eq σ τ VX DX VY DY
  have hStrict : StrictFunctionTerms = Strictness.StrictFunctionTerms :=
    funext fun σ => funext fun τ => funext fun VA => funext fun VX =>
      funext fun DY => strictFunctionTerms_eq σ τ VA VX DY
  simp only [model, operationalModel, hDiv, numeralTerms_eq, hPair, hFun, hStrict]


theorem V_eq (τ : Ty) : V τ = Strictness.V τ := by
  have transport : ∀ M N : LogicalModel, M = N →
      HEq (M.acceptable τ) (N.acceptable τ) := by
    intro M N h
    cases h
    rfl
  exact eq_of_heq (transport model operationalModel model_eq)

theorem D_eq (τ : Ty) : D τ = Strictness.D τ := by
  have transport : ∀ M N : LogicalModel, M = N →
      HEq (M.divergentSide τ) (N.divergentSide τ) := by
    intro M N h
    cases h
    rfl
  exact eq_of_heq (transport model operationalModel model_eq)

end Strictness.SmallStep
