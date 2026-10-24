import Strictness.Language.Type

namespace Strictness

open Usage
open scoped Classical

/-- Predicates on the (untyped) closed terms of a semantic model. -/
abbrev TermSet (α : Type) := α → Prop

namespace TermSet

def empty : TermSet α := fun _ => False
def union (X Y : TermSet α) : TermSet α := fun t => X t ∨ Y t

@[ext] theorem ext {X Y : TermSet α} (h : ∀ t, X t ↔ Y t) : X = Y := by
  funext t
  apply propext
  exact h t

end TermSet

/--
The sets used to interpret annotated types.

`functionValue` combines the V-to-V and D-to-D obligations of the function
clause; `functionStrict` expresses the extra V-to-D obligation for a strict
arrow. `operationalModel` in `Strictness/Semantics/Interpretation.lean` instantiates this interface
with call-by-name value and error evaluation.
-/
structure LogicalModel where
  carrier : Type
  allTerms : SimpleTy → TermSet carrier
  diverges : SimpleTy → TermSet carrier
  numeral : TermSet carrier
  pairValue : SimpleTy → SimpleTy → TermSet carrier → TermSet carrier → TermSet carrier
  functionValue :
    SimpleTy → SimpleTy →
    TermSet carrier → TermSet carrier → TermSet carrier → TermSet carrier → TermSet carrier
  functionStrict :
    SimpleTy → SimpleTy →
    TermSet carrier → TermSet carrier → TermSet carrier → TermSet carrier

namespace LogicalModel

mutual
/-- The value-side interpretation `V(τ)`. -/
noncomputable def acceptable (M : LogicalModel) : Ty → TermSet M.carrier
  | .int u =>
      if lazy ≤ u then M.allTerms .int
      else TermSet.union (M.diverges .int) M.numeral
  | .prod σ τ u =>
      if lazy ≤ u then M.allTerms (.prod σ.erase τ.erase)
      else TermSet.union (M.diverges (.prod σ.erase τ.erase))
        (M.pairValue σ.erase τ.erase (acceptable M σ) (acceptable M τ))
  | .arrow σ τ u =>
      if lazy ≤ u then M.allTerms (.arrow σ.erase τ.erase)
      else TermSet.union (M.diverges (.arrow σ.erase τ.erase))
        (M.functionValue σ.erase τ.erase (acceptable M σ) (divergentSide M σ)
          (acceptable M τ) (divergentSide M τ))

/-- The divergence-side interpretation `D(τ)`. -/
noncomputable def divergentSide (M : LogicalModel) : Ty → TermSet M.carrier
  | .int u =>
      if Ty.IsLazy (.int u) then TermSet.empty
      else if lazy ≤ u then M.allTerms .int
      else match u with
        | strict => M.diverges .int
        | _ => TermSet.empty
  | .prod σ τ u =>
      if Ty.IsLazy (.prod σ τ u) then TermSet.empty
      else if lazy ≤ u then M.allTerms (.prod σ.erase τ.erase)
      else match u with
        | unknown | strict =>
            TermSet.union (M.diverges (.prod σ.erase τ.erase))
              (TermSet.union
                (M.pairValue σ.erase τ.erase (divergentSide M σ) (acceptable M τ))
                (M.pairValue σ.erase τ.erase (acceptable M σ) (divergentSide M τ)))
        | lazy | top => TermSet.empty
  | .arrow σ τ u =>
      if Ty.IsLazy (.arrow σ τ u) then TermSet.empty
      else if lazy ≤ u then M.allTerms (.arrow σ.erase τ.erase)
      else match u with
        | strict =>
            TermSet.union (M.diverges (.arrow σ.erase τ.erase))
              (M.functionStrict σ.erase τ.erase
                (acceptable M (.arrow σ τ strict))
                (acceptable M σ)
                (divergentSide M τ))
        | unknown | lazy | top => TermSet.empty
end

theorem acceptable_eq_allTerms_of_outer_lazy (M : LogicalModel) {τ : Ty}
    (h : lazy ≤ τ.outer) : acceptable M τ = M.allTerms τ.erase := by
  cases τ with
  | int u =>
      change lazy ≤ u at h
      simp only [acceptable, if_pos h]
      rfl
  | prod σ τ u =>
      change lazy ≤ u at h
      simp only [acceptable, if_pos h]
      rfl
  | arrow σ τ u =>
      change lazy ≤ u at h
      simp only [acceptable, if_pos h]
      rfl

theorem divergentSide_eq_empty_of_lazy (M : LogicalModel) {τ : Ty} (h : τ.IsLazy) :
    divergentSide M τ = TermSet.empty := by
  cases τ with
  | int u =>
      unfold divergentSide
      rw [if_pos h]
  | prod σ τ u =>
      unfold divergentSide
      rw [if_pos h]
  | arrow σ τ u =>
      unfold divergentSide
      rw [if_pos h]

theorem divergentSide_eq_allTerms_of_not_lazy (M : LogicalModel) {τ : Ty}
    (hNotLazy : ¬ τ.IsLazy) (hOuter : lazy ≤ τ.outer) :
    divergentSide M τ = M.allTerms τ.erase := by
  cases τ with
  | int u =>
      change ¬ Ty.IsLazy (.int u) at hNotLazy
      change lazy ≤ u at hOuter
      unfold divergentSide
      rw [if_neg hNotLazy, if_pos hOuter]
      rfl
  | prod σ τ u =>
      change ¬ Ty.IsLazy (.prod σ τ u) at hNotLazy
      change lazy ≤ u at hOuter
      unfold divergentSide
      rw [if_neg hNotLazy, if_pos hOuter]
      rfl
  | arrow σ τ u =>
      change ¬ Ty.IsLazy (.arrow σ τ u) at hNotLazy
      change lazy ≤ u at hOuter
      unfold divergentSide
      rw [if_neg hNotLazy, if_pos hOuter]
      rfl

theorem top_scale_not_lazy (τ : Ty) : ¬ (τ.scale top).IsLazy := by
  cases τ with
  | int u =>
      change ¬ Usage.Le (Usage.scale top u) lazy
      exact Usage.top_scale_not_le_lazy u
  | prod σ τ u =>
      intro h
      change Usage.Le (Usage.scale top u) lazy ∧ _ ∧ _ at h
      exact Usage.top_scale_not_le_lazy u h.1
  | arrow σ τ u =>
      change ¬ Usage.Le (Usage.scale top u) lazy
      exact Usage.top_scale_not_le_lazy u

/-- The structural scaling identity `D(? ∗ τ) = ∅`. -/
theorem divergentSide_unknown_scale (M : LogicalModel) (τ : Ty) :
    divergentSide M (τ.scale unknown) = TermSet.empty :=
  divergentSide_eq_empty_of_lazy M (Ty.unknown_scale_lazy τ)

/-- The structural scaling identity `D(L ∗ τ) = ∅`. -/
theorem divergentSide_lazy_scale (M : LogicalModel) (τ : Ty) :
    divergentSide M (τ.scale lazy) = TermSet.empty :=
  divergentSide_eq_empty_of_lazy M (Ty.lazy_scale_lazy τ)

/-- The structural scaling identity `V(S ∗ τ) = V(τ)`. -/
theorem acceptable_strict_scale (M : LogicalModel) (τ : Ty) :
    acceptable M (τ.scale strict) = acceptable M τ := by
  rw [Ty.strict_scale]

/-- The structural scaling identity `D(S ∗ τ) = D(τ)`. -/
theorem divergentSide_strict_scale (M : LogicalModel) (τ : Ty) :
    divergentSide M (τ.scale strict) = divergentSide M τ := by
  rw [Ty.strict_scale]

/-- The structural scaling identity `V(? ∗ τ) = V(τ)`. -/
theorem acceptable_unknown_scale (M : LogicalModel) (τ : Ty) :
    acceptable M (τ.scale unknown) = acceptable M τ := by
  induction τ with
  | int u =>
      cases u <;> simp only [Ty.scale, Usage.scale, acceptable,
        if_neg Usage.not_lazy_le_unknown, if_neg Usage.not_lazy_le_strict,
        if_pos Usage.lazy_le_lazy, if_pos Usage.lazy_le_top]
  | prod σ τ u ihσ ihτ =>
      cases u with
      | unknown =>
          simp only [Ty.scale, Usage.scale, acceptable,
            if_neg Usage.not_lazy_le_unknown]
          rw [ihσ, ihτ]
          simp only [Ty.erase_scale]
      | strict =>
          simp only [Ty.scale, Usage.scale, acceptable,
            if_neg Usage.not_lazy_le_unknown, if_neg Usage.not_lazy_le_strict]
          rw [ihσ, ihτ]
          simp only [Ty.erase_scale]
      | lazy =>
          calc
            acceptable M ((Ty.prod σ τ lazy).scale unknown) =
                M.allTerms ((Ty.prod σ τ lazy).scale unknown).erase :=
              acceptable_eq_allTerms_of_outer_lazy M (by
                rw [Ty.outer_scale]
                change Usage.Le lazy (Usage.scale unknown lazy)
                trivial)
            _ = M.allTerms (Ty.prod σ τ lazy).erase := by rw [Ty.erase_scale]
            _ = acceptable M (Ty.prod σ τ lazy) :=
              (acceptable_eq_allTerms_of_outer_lazy M (τ := Ty.prod σ τ lazy)
                Usage.lazy_le_lazy).symm
      | top =>
          calc
            acceptable M ((Ty.prod σ τ top).scale unknown) =
                M.allTerms ((Ty.prod σ τ top).scale unknown).erase :=
              acceptable_eq_allTerms_of_outer_lazy M (by
                rw [Ty.outer_scale]
                change Usage.Le lazy (Usage.scale unknown top)
                trivial)
            _ = M.allTerms (Ty.prod σ τ top).erase := by rw [Ty.erase_scale]
            _ = acceptable M (Ty.prod σ τ top) :=
              (acceptable_eq_allTerms_of_outer_lazy M (τ := Ty.prod σ τ top)
                Usage.lazy_le_top).symm
  | arrow σ τ u =>
      cases u <;> simp only [Ty.scale, Usage.scale, acceptable,
        if_neg Usage.not_lazy_le_unknown, if_neg Usage.not_lazy_le_strict,
        if_pos Usage.lazy_le_lazy, if_pos Usage.lazy_le_top]

/-- The structural scaling identity `V(L ∗ τ) = U_τ`. -/
theorem acceptable_lazy_scale (M : LogicalModel) (τ : Ty) :
    acceptable M (τ.scale lazy) = M.allTerms τ.erase := by
  calc
    acceptable M (τ.scale lazy) = M.allTerms (τ.scale lazy).erase :=
      acceptable_eq_allTerms_of_outer_lazy M (by
        rw [Ty.outer_scale]
        exact Usage.lazy_le_lazy_scale τ.outer)
    _ = M.allTerms τ.erase := by rw [Ty.erase_scale]

/-- The structural scaling identity `V(⊤ ∗ τ) = U_τ`. -/
theorem acceptable_top_scale (M : LogicalModel) (τ : Ty) :
    acceptable M (τ.scale top) = M.allTerms τ.erase := by
  calc
    acceptable M (τ.scale top) = M.allTerms (τ.scale top).erase :=
      acceptable_eq_allTerms_of_outer_lazy M (by
        rw [Ty.outer_scale]
        exact Usage.lazy_le_top_scale τ.outer)
    _ = M.allTerms τ.erase := by rw [Ty.erase_scale]

/-- The structural scaling identity `D(⊤ ∗ τ) = U_τ`. -/
theorem divergentSide_top_scale (M : LogicalModel) (τ : Ty) :
    divergentSide M (τ.scale top) = M.allTerms τ.erase := by
  calc
    divergentSide M (τ.scale top) = M.allTerms (τ.scale top).erase :=
      divergentSide_eq_allTerms_of_not_lazy M (top_scale_not_lazy τ) (by
        rw [Ty.outer_scale]
        exact Usage.lazy_le_top_scale τ.outer)
    _ = M.allTerms τ.erase := by rw [Ty.erase_scale]

end LogicalModel
end Strictness
