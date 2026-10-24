import Strictness.Semantics.SemanticBasic
import Strictness.Semantics.SemanticSubtype
import Strictness.Semantics.SemanticCap
import Strictness.Semantics.SemanticApplication
import Strictness.Semantics.SemanticPlusEnv
import Strictness.Semantics.SemanticPlusD

namespace Strictness

open Usage
open Term

/-- D-members are acceptable members. -/
theorem definite_D_subset_V :
    ∀ τ : Ty, TermSet.Subset (D τ) (V τ) := D_subset_V

/-- Lazy types have no D-side members. -/
theorem definite_lazy_implies_D_empty {τ : Ty} (h : Ty.IsLazy τ) :
    D τ = TermSet.empty := lazy_implies_D_empty h

/-- A D-set is empty exactly when its type is Lazy. -/
theorem definite_D_empty_iff_lazy {τ : Ty} :
    D τ = TermSet.empty ↔ Ty.IsLazy τ := D_empty_iff_lazy

/-- Divergent terms belong to D at every non-Lazy type. -/
theorem definite_not_lazy_O_subset_D {τ : Ty} (h : ¬ Ty.IsLazy τ) :
    TermSet.Subset (DivergentTerms τ.erase) (D τ) :=
  divergentTerms_subset_D_of_not_lazy h

/-- The D-set of a type sum is contained in the union of the operand D-sets. -/
theorem definite_plus_D {σ τ ρ : Ty} (h : Ty.plus σ τ = some ρ) :
    TermSet.Subset (D ρ) (TermSet.union (D σ) (D τ)) :=
  semantic_plus_D h

/-- A D-witness in a meet-combined environment can be transported to both
component environments. -/
theorem definite_D_cap_env_split {Γ₁ Γ₂ Γ : Env} {ρ : Substitution}
    (hcap : Env.cap Γ₁ Γ₂ = some Γ) (hD : SatisfiesD Γ ρ) :
    SatisfiesD Γ₁ ρ ∧ SatisfiesD Γ₂ ρ :=
  satisfiesD_cap_split hcap hD

/-- Every divergent term belongs to D for a strict or top outer annotation. -/
theorem definite_divergence_D_strict_top {τ : Ty}
    (hOuter : τ.outer = strict ∨ τ.outer = top) :
    TermSet.Subset (DivergentTerms τ.erase) (D τ) :=
  divergentTerms_subset_D_of_outer_strict_or_top hOuter

/-- Scaling by unknown empties the D-set. -/
theorem definite_D_unknown_scale (τ : Ty) :
    D (τ.scale unknown) = TermSet.empty :=
  LogicalModel.divergentSide_unknown_scale operationalModel τ

theorem definite_D_lazy_scale (τ : Ty) :
    D (τ.scale lazy) = TermSet.empty :=
  LogicalModel.divergentSide_lazy_scale operationalModel τ

theorem definite_D_strict_scale (τ : Ty) :
    D (τ.scale strict) = D τ :=
  LogicalModel.divergentSide_strict_scale operationalModel τ

theorem definite_D_top_scale (τ : Ty) :
    D (τ.scale top) = AllTerms τ.erase :=
  LogicalModel.divergentSide_top_scale operationalModel τ

/-- A strict outer result admits Ω on the D-side. -/
theorem definite_omega_mem_D_of_outer_strict {τ : Ty}
    (hOuter : τ.outer = strict) : D τ .omega :=
  omega_mem_D_of_outer_strict hOuter


end Strictness
