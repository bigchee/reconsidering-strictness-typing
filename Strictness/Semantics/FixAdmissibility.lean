import Strictness.Semantics.UnfoldingAdmissibility

namespace Strictness

open Usage
open scoped Classical

/-- V and D are admissible for delayed finite-unfolding families.
The induction is on the usage type. -/
theorem semantic_unfold_admissible (τ : Ty) :
    UnfoldAdmissible τ.erase (V τ) ∧ UnfoldAdmissible τ.erase (D τ) := by
  induction τ with
  | int u =>
      constructor
      · unfold V LogicalModel.acceptable operationalModel
        by_cases hOuter : lazy ≤ u
        · rw [if_pos hOuter]
          exact UnfoldAdmissible.allTerms .int
        · rw [if_neg hOuter]
          exact UnfoldAdmissible.safe_numeral
      · unfold D LogicalModel.divergentSide operationalModel
        by_cases hLazy : Ty.IsLazy (.int u)
        · rw [if_pos hLazy]
          exact UnfoldAdmissible.empty .int
        · rw [if_neg hLazy]
          by_cases hOuter : lazy ≤ u
          · rw [if_pos hOuter]
            exact UnfoldAdmissible.allTerms .int
          · rw [if_neg hOuter]
            cases u with
            | strict => exact UnfoldAdmissible.divergentTerms .int
            | unknown => exact UnfoldAdmissible.empty .int
            | lazy => exact UnfoldAdmissible.empty .int
            | top => exact UnfoldAdmissible.empty .int
  | prod σ τ u ihσ ihτ =>
      have hV : UnfoldAdmissible (Ty.prod σ τ u).erase (V (.prod σ τ u)) := by
        unfold V LogicalModel.acceptable operationalModel
        by_cases hOuter : lazy ≤ u
        · rw [if_pos hOuter]
          exact UnfoldAdmissible.allTerms _
        · rw [if_neg hOuter]
          exact UnfoldAdmissible.safe_pair ihσ.1 ihτ.1
      refine ⟨hV, ?_⟩
      unfold D LogicalModel.divergentSide operationalModel
      by_cases hLazy : Ty.IsLazy (.prod σ τ u)
      · rw [if_pos hLazy]
        exact UnfoldAdmissible.empty _
      · rw [if_neg hLazy]
        by_cases hOuter : lazy ≤ u
        · rw [if_pos hOuter]
          exact UnfoldAdmissible.allTerms _
        · rw [if_neg hOuter]
          cases u with
          | unknown | strict =>
              exact UnfoldAdmissible.safe_union
                (UnfoldAdmissible.safe_pair ihσ.2 ihτ.1)
                (UnfoldAdmissible.safe_pair ihσ.1 ihτ.2)
          | lazy => exact UnfoldAdmissible.empty _
          | top => exact UnfoldAdmissible.empty _
  | arrow σ τ u ihσ ihτ =>
      have hV : UnfoldAdmissible (Ty.arrow σ τ u).erase (V (.arrow σ τ u)) := by
        unfold V LogicalModel.acceptable operationalModel
        by_cases hOuter : lazy ≤ u
        · rw [if_pos hOuter]
          exact UnfoldAdmissible.allTerms _
        · rw [if_neg hOuter]
          exact UnfoldAdmissible.safe_function
            (V_subset_allTerms σ) (D_subset_allTerms σ) ihτ.1 ihτ.2
      refine ⟨hV, ?_⟩
      unfold D LogicalModel.divergentSide operationalModel
      by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
      · rw [if_pos hLazy]
        exact UnfoldAdmissible.empty _
      · rw [if_neg hLazy]
        by_cases hOuter : lazy ≤ u
        · rw [if_pos hOuter]
          exact UnfoldAdmissible.allTerms _
        · rw [if_neg hOuter]
          cases u with
          | strict =>
              exact UnfoldAdmissible.safe_strict_function hV
                (divergentTerms_subset_V (.arrow σ τ strict))
                (V_subset_allTerms σ) ihτ.2
          | unknown => exact UnfoldAdmissible.empty _
          | lazy => exact UnfoldAdmissible.empty _
          | top => exact UnfoldAdmissible.empty _

/-- Cofinal V-membership passes to the limit of an unfolding family. -/
theorem unfoldFamily_mem_V_of_cofinal
    {τ : Ty} {A : SimpleTy} {body : Term} {f : Nat → Term} {e : Term}
    (hFix : AllTerms A (.fix body)) (hFamily : UnfoldFamily body f e)
    (hAll : AllTerms τ.erase e) (hMem : Cofinal (fun n => V τ (f n))) :
    V τ e :=
  (semantic_unfold_admissible τ).1 hFix hFamily hAll hMem

/-- Cofinal D-membership passes to the limit of an unfolding family. -/
theorem unfoldFamily_mem_D_of_cofinal
    {τ : Ty} {A : SimpleTy} {body : Term} {f : Nat → Term} {e : Term}
    (hFix : AllTerms A (.fix body)) (hFamily : UnfoldFamily body f e)
    (hAll : AllTerms τ.erase e) (hMem : Cofinal (fun n => D τ (f n))) :
    D τ e :=
  (semantic_unfold_admissible τ).2 hFix hFamily hAll hMem

/-- The V-admissibility statement used by the fix-rule proof. -/
theorem fixApprox_mem_V_of_cofinal {τ : Ty} {body : Term}
    (hFix : AllTerms τ.erase (.fix body))
    (hMem : Cofinal (fun n => V τ (Term.fixApprox body n))) :
    V τ (.fix body) := by
  have hFamily : UnfoldFamily body (fun n => Term.fixApprox body n) (.fix body) := by
    simpa only [Nat.sub_zero] using (UnfoldFamily.hole (body := body) 0)
  exact unfoldFamily_mem_V_of_cofinal hFix hFamily hFix hMem

/-- The D-admissibility statement used by the fix-rule proof. -/
theorem fixApprox_mem_D_of_cofinal {τ : Ty} {body : Term}
    (hFix : AllTerms τ.erase (.fix body))
    (hMem : Cofinal (fun n => D τ (Term.fixApprox body n))) :
    D τ (.fix body) := by
  have hFamily : UnfoldFamily body (fun n => Term.fixApprox body n) (.fix body) := by
    simpa only [Nat.sub_zero] using (UnfoldFamily.hole (body := body) 0)
  exact unfoldFamily_mem_D_of_cofinal hFix hFamily hFix hMem

theorem fixApprox_mem_V_limit {τ : Ty} {body : Term}
    (hFix : AllTerms τ.erase (.fix body))
    (hMem : ∀ n, V τ (Term.fixApprox body n)) : V τ (.fix body) := by
  apply fixApprox_mem_V_of_cofinal hFix
  intro N
  exact ⟨N, Nat.le_refl N, hMem N⟩

theorem fixApprox_mem_D_limit {τ : Ty} {body : Term}
    (hFix : AllTerms τ.erase (.fix body))
    (hMem : ∀ n, D τ (Term.fixApprox body n)) : D τ (.fix body) := by
  apply fixApprox_mem_D_of_cofinal hFix
  intro N
  exact ⟨N, Nat.le_refl N, hMem N⟩

end Strictness
