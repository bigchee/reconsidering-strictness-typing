import Strictness.Operational.Properties
import Strictness.Semantics.Interpretation

namespace Strictness.SmallStep

/- The observation-based sets below use the existing `AllTerms` domain.
Only big-step observations are replaced by finite or infinite source reductions. -/
/-- Divergent closed terms of a given simple type. -/
def DivergentTerms (τ : SimpleTy) : TermSet Term :=
  fun e => AllTerms τ e ∧ InfiniteSteps e

/-- Closed terms that reduce to an integer value. -/
def NumeralTerms : TermSet Term :=
  fun e => Term.Closed e ∧ Term.HasType [] e .int ∧ ∃ n, Steps e (.int n)

/-- Terms reducing to a pair whose retained components belong to two sets. -/
def PairTerms (σ τ : SimpleTy) (X Y : TermSet Term) : TermSet Term :=
  fun e => AllTerms (.prod σ τ) e ∧ ∃ e₁ e₂, Steps e (.pair e₁ e₂) ∧ X e₁ ∧ Y e₂

/-- Terms reducing to a function satisfying both V and D obligations. -/
def FunctionTerms (σ τ : SimpleTy)
    (VX DX VY DY : TermSet Term) : TermSet Term :=
  fun e =>
    AllTerms (.arrow σ τ) e ∧
    ∃ body,
      Steps e (.lam body) ∧
      (∀ a, VX a → VY (.app e a)) ∧
      (∀ a, DX a → DY (.app e a))

/-- Terms denoting a strict function in the sense used in `D` for an `S` arrow. -/
def StrictFunctionTerms (_σ _τ : SimpleTy)
    (VArrow VX DY : TermSet Term) : TermSet Term :=
  fun e =>
    VArrow e ∧
    ∃ body,
      Steps e (.lam body) ∧
      (∀ a, VX a → DY (.app e a))

/-- The same logical-model interface instantiated with small-step observations. -/
def model : LogicalModel where
  carrier := Term
  allTerms := AllTerms
  diverges := fun A => DivergentTerms A
  numeral := NumeralTerms
  pairValue := fun σ τ X Y => PairTerms σ τ X Y
  functionValue := fun σ τ VX DX VY DY => FunctionTerms σ τ VX DX VY DY
  functionStrict := fun σ τ VA VX DY => StrictFunctionTerms σ τ VA VX DY

noncomputable def V : Ty → TermSet Term := LogicalModel.acceptable model
noncomputable def D : Ty → TermSet Term := LogicalModel.divergentSide model

end Strictness.SmallStep
