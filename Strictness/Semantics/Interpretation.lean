import Strictness.Operational.BigStep
import Strictness.Semantics.LogicalRelation

namespace Strictness

open Usage
open Term
open scoped Classical

/-- The erased simple type of a semantic closed term. -/
def AllTerms (τ : SimpleTy) : TermSet Term :=
  fun e => Term.Closed e ∧ Term.HasType [] e τ

/-- Divergent closed terms of a given simple type. -/
def DivergentTerms (τ : SimpleTy) : TermSet Term :=
  fun e => AllTerms τ e ∧ Term.Diverges e

/-- Closed terms that evaluate to an integer value. -/
def NumeralTerms : TermSet Term :=
  fun e => Term.Closed e ∧ Term.HasType [] e .int ∧ ∃ n, Eval e (.int n)

/-- Terms evaluating to a pair whose retained components belong to two sets. -/
def PairTerms (σ τ : SimpleTy) (X Y : TermSet Term) : TermSet Term :=
  fun e => AllTerms (.prod σ τ) e ∧ ∃ e₁ e₂, Eval e (.pair e₁ e₂) ∧ X e₁ ∧ Y e₂

/-- Terms evaluating to a function satisfying both V and D obligations. -/
def FunctionTerms (σ τ : SimpleTy)
    (VX DX VY DY : TermSet Term) : TermSet Term :=
  fun e =>
    AllTerms (.arrow σ τ) e ∧
    ∃ body,
      Eval e (.lam body) ∧
      (∀ a, VX a → VY (.app e a)) ∧
      (∀ a, DX a → DY (.app e a))

/-- Terms denoting a strict function in the sense used in `D` for an `S` arrow. -/
def StrictFunctionTerms (_σ _τ : SimpleTy)
    (VArrow VX DY : TermSet Term) : TermSet Term :=
  fun e =>
    VArrow e ∧
    ∃ body,
      Eval e (.lam body) ∧
      (∀ a, VX a → DY (.app e a))

/-- Instantiate the semantic-set interface with the call-by-name value
and error evaluations of `Strictness/Operational/BigStep.lean`. -/
def operationalModel : LogicalModel where
  carrier := Term
  allTerms := AllTerms
  diverges := DivergentTerms
  numeral := NumeralTerms
  pairValue := fun σ τ X Y => PairTerms σ τ X Y
  functionValue := fun σ τ VX DX VY DY =>
    FunctionTerms σ τ VX DX VY DY
  functionStrict := fun σ τ VArrow VX DY =>
    StrictFunctionTerms σ τ VArrow VX DY

/-- The semantic sets induced by the concrete operational model. -/
noncomputable def V : Ty → TermSet Term := LogicalModel.acceptable operationalModel
noncomputable def D : Ty → TermSet Term := LogicalModel.divergentSide operationalModel

@[simp] theorem V_def (τ : Ty) : V τ = LogicalModel.acceptable operationalModel τ := rfl
@[simp] theorem D_def (τ : Ty) : D τ = LogicalModel.divergentSide operationalModel τ := rfl

end Strictness
