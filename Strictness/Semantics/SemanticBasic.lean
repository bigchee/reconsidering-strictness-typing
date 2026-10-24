import Strictness.Semantics.SemanticLemmas

namespace Strictness

open Usage
open Term

/-- Every divergent closed term belongs to the acceptable set of the
corresponding type. This is the generic divergence branch present in every
non-Lazy acceptable set; Lazy types have no divergent-side requirement here. -/
theorem divergentTerms_subset_V :
    ∀ τ : Ty, TermSet.Subset (DivergentTerms τ.erase) (V τ)
  | .int u => by
      intro e he
      unfold V LogicalModel.acceptable operationalModel
      by_cases h : lazy ≤ u
      · simp only [h, if_pos]
        exact he.1
      · simp only [h]
        exact Or.inl he
  | .prod σ τ u => by
      intro e he
      unfold V LogicalModel.acceptable operationalModel
      by_cases h : lazy ≤ u
      · simp only [h, if_pos]
        exact he.1
      · simp only [h]
        exact Or.inl he
  | .arrow σ τ u => by
      intro e he
      unfold V LogicalModel.acceptable operationalModel
      by_cases h : lazy ≤ u
      · simp only [h, if_pos]
        exact he.1
      · simp only [h]
        exact Or.inl he


/-- Every divergent term belongs to the corresponding erased simple-type set. -/
theorem divergentTerms_subset_allTerms (τ : SimpleTy) :
    TermSet.Subset (DivergentTerms τ) (AllTerms τ) := by
  intro e h
  exact h.1

/-- Every numeral term belongs to the corresponding erased simple-type set. -/
theorem numeralTerms_subset_allTerms :
    TermSet.Subset NumeralTerms (AllTerms .int) := by
  intro e h
  exact ⟨h.1, h.2.1⟩

/-- Every semantic pair term belongs to its erased pair type. -/
theorem pairTerms_subset_allTerms (σ τ : SimpleTy)
    (X Y : TermSet Term) :
    TermSet.Subset (PairTerms σ τ X Y) (AllTerms (.prod σ τ)) := by
  intro e h
  exact h.1

/-- Every semantic function term belongs to its erased arrow type. -/
theorem functionTerms_subset_allTerms (σ τ : SimpleTy)
    (VX DX VY DY : TermSet Term) :
    TermSet.Subset (FunctionTerms σ τ VX DX VY DY) (AllTerms (.arrow σ τ)) := by
  intro e h
  exact h.1

/-- Every strict-function semantic term belongs to its erased arrow type. -/
theorem strictFunctionTerms_subset_allTerms {σ τ : SimpleTy}
    {VArrow VX DY : TermSet Term}
    (hVA : TermSet.Subset VArrow (AllTerms (.arrow σ τ))) :
    TermSet.Subset (StrictFunctionTerms σ τ VArrow VX DY) (AllTerms (.arrow σ τ)) := by
  intro e h
  exact hVA h.1

/-- Every V-member is a closed term of the erased simple type. -/
theorem V_subset_allTerms : ∀ τ : Ty, TermSet.Subset (V τ) (AllTerms τ.erase)
  | .int u => by
      intro e he
      unfold V LogicalModel.acceptable operationalModel at he
      by_cases h : lazy ≤ u
      · simpa [h] using he
      · simp only [h] at he
        rcases he with hdiv | hnum
        · exact hdiv.1
        · exact ⟨hnum.1, hnum.2.1⟩
  | .prod σ τ u => by
      intro e he
      unfold V LogicalModel.acceptable operationalModel at he
      by_cases h : lazy ≤ u
      · simpa [h] using he
      · simp only [h] at he
        rcases he with hdiv | hpair
        · exact hdiv.1
        · exact hpair.1
  | .arrow σ τ u => by
      intro e he
      unfold V LogicalModel.acceptable operationalModel at he
      by_cases h : lazy ≤ u
      · simpa [h] using he
      · simp only [h] at he
        rcases he with hdiv | hfun
        · exact hdiv.1
        · exact hfun.1

/-- Every D-member is a closed term of the erased simple type. -/
theorem D_subset_allTerms : ∀ τ : Ty, TermSet.Subset (D τ) (AllTerms τ.erase)
  | .int u => by
      intro e he
      unfold D LogicalModel.divergentSide operationalModel at he
      by_cases hLazy : Ty.IsLazy (.int u)
      · simp only [hLazy, if_pos] at he
        exact False.elim he
      · simp only [hLazy] at he
        by_cases hOuter : lazy ≤ u
        · simp only [hOuter, if_pos] at he
          exact he
        · simp only [hOuter] at he
          cases u with
            | strict => exact he.1
            | unknown => exact False.elim he
            | lazy => exact False.elim he
            | top => exact False.elim he
  | .prod σ τ u => by
      intro e he
      unfold D LogicalModel.divergentSide operationalModel at he
      by_cases hLazy : Ty.IsLazy (.prod σ τ u)
      · simp only [hLazy, if_pos] at he
        exact False.elim he
      · simp only [hLazy] at he
        by_cases hOuter : lazy ≤ u
        · simp only [hOuter, if_pos] at he
          exact he
        · simp only [hOuter] at he
          cases u with
          | unknown | strict =>
              rcases he with hdiv | hpair
              · exact hdiv.1
              · rcases hpair with hpair | hpair
                · exact hpair.1
                · exact hpair.1
          | lazy => exact False.elim he
          | top => exact False.elim he
  | .arrow σ τ u => by
      intro e he
      unfold D LogicalModel.divergentSide operationalModel at he
      by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
      · simp only [hLazy, if_pos] at he
        exact False.elim he
      · simp only [hLazy] at he
        by_cases hOuter : lazy ≤ u
        · simp only [hOuter, if_pos] at he
          exact he
        · simp only [hOuter] at he
          cases u with
          | strict =>
              rcases he with hdiv | hfun
              · exact hdiv.1
              · exact V_subset_allTerms (.arrow σ τ strict) hfun.1
          | unknown => exact False.elim he
          | lazy => exact False.elim he
          | top => exact False.elim he

/-- `D((σ → τ)^?)` is empty because an arrow with outer `?` is Lazy. -/
theorem D_arrow_unknown_eq_empty (σ τ : Ty) :
    D (Ty.arrow σ τ unknown) = TermSet.empty := by
  rw [D_def]
  apply LogicalModel.divergentSide_eq_empty_of_lazy operationalModel
  simp [Ty.IsLazy, Usage.Le]

/-- Every D-set is contained in the
corresponding V-set. This deliberately does not assert anything about when
D is empty. -/
theorem D_subset_V : ∀ τ : Ty, TermSet.Subset (D τ) (V τ)
  | .int u => by
      intro e he
      unfold D LogicalModel.divergentSide operationalModel at he
      unfold V LogicalModel.acceptable operationalModel
      by_cases hLazy : Ty.IsLazy (.int u)
      · simp only [hLazy, if_pos] at he
        exact False.elim he
      · simp only [hLazy] at he
        by_cases hOuter : lazy ≤ u
        · simp only [hOuter, if_pos] at he ⊢
          exact he
        · simp only [hOuter] at he ⊢
          cases u with
          | unknown => exact False.elim he
          | strict =>
              simp only [if_false, TermSet.union] at he ⊢
              exact Or.inl he
          | lazy => exact False.elim he
          | top => exact False.elim he
  | .prod σ τ u => by
      intro e he
      unfold D LogicalModel.divergentSide operationalModel at he
      unfold V LogicalModel.acceptable operationalModel
      by_cases hLazy : Ty.IsLazy (.prod σ τ u)
      · simp only [hLazy, if_pos] at he
        exact False.elim he
      · simp only [hLazy] at he
        by_cases hOuter : lazy ≤ u
        · simp only [hOuter, if_pos] at he ⊢
          exact he
        · simp only [hOuter] at he ⊢
          cases u with
          | unknown | strict =>
              rcases he with hdiv | hpair
              · exact Or.inl hdiv
              · rcases hpair with hpair | hpair
                · rcases hpair with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
                  exact Or.inr ⟨hAll, e₁, e₂, hev, (D_subset_V σ h₁), h₂⟩
                · rcases hpair with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
                  exact Or.inr ⟨hAll, e₁, e₂, hev, h₁, (D_subset_V τ h₂)⟩
          | lazy => exact False.elim he
          | top => exact False.elim he
  | .arrow σ τ u => by
      intro e he
      unfold D LogicalModel.divergentSide operationalModel at he
      unfold V LogicalModel.acceptable operationalModel
      by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
      · simp only [hLazy, if_pos] at he
        exact False.elim he
      · simp only [hLazy] at he
        by_cases hOuter : lazy ≤ u
        · simp only [hOuter, if_pos] at he ⊢
          exact he
        · simp only [hOuter] at he ⊢
          cases u with
          | unknown => exact False.elim he
          | lazy => exact False.elim he
          | top => exact False.elim he
          | strict =>
              rcases he with hdiv | hfun
              · exact Or.inl hdiv
              · have hVArrow := hfun.1
                unfold V LogicalModel.acceptable at hVArrow
                simp only [Usage.not_lazy_le_strict, if_false,
                  TermSet.union] at hVArrow
                rcases hVArrow with hdiv | hfunValue
                · exact Or.inl hdiv
                · exact Or.inr hfunValue

end Strictness
